//! Translation of optimized MIR into verification conditions (SPEC.md §5).
//!
//! This covers a small subset: functions whose parameters and locals are
//! integers or booleans, with straight-line code, `if`, `Goto`, and `Return`. Each
//! `assert` in MIR becomes a VC, which is the same as an overflow check. Loops,
//! calls, references, multiplication, and division are reported as unsupported.
//!
//! The walk is symbolic. Each path through the function carries a state that maps
//! MIR locals to expressions and a list of branch conditions. A VC is emitted for
//! every assertion, under the path conditions and the range of each integer
//! parameter. The VC is only as strong as this translation, and Z3 checks it.

use std::collections::HashMap;
use std::fmt;

use rustc_attr_ir::{Attribute, AttributeKind};
use rustc_hir::def_id::DefId;
use rustc_index::Idx;
use rustc_middle::mir::{
    BasicBlock, BinOp, Body, Local, Operand, Place, PlaceElem, Rvalue, StatementKind,
    TerminatorKind, VarDebugInfoContents,
};
use rustc_middle::ty::{self, IntTy, Ty, TyCtxt, TypingEnv, UintTy};
use tpt_proof_contract::spec;
use tpt_proof_contract::{Expr, Sort, Vc};

/// Why a function is outside the subset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unsupported(pub String);

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

fn unsupported<T>(reason: impl Into<String>) -> Result<T, Unsupported> {
    Err(Unsupported(reason.into()))
}

/// Translates a function to VCs, one per assertion on each path through it.
pub fn translate(tcx: TyCtxt<'_>, def_id: DefId) -> Result<Vec<Vc>, Unsupported> {
    let body = tcx.optimized_mir(def_id);
    let name = tcx.def_path_str(def_id);
    let (requires, ensures) = contracts(tcx, def_id);

    let mut params = Vec::new();
    let mut ranges = Vec::new();
    let mut locals = HashMap::new();
    for index in 1..=body.arg_count {
        let local = Local::new(index);
        let ty = body.local_decls[local].ty;
        let var = format!("_{index}");
        let sort = sort_of(ty)?;
        params.push((var.clone(), sort));
        if let Some((lo, hi)) = int_range(ty)? {
            ranges.push(in_range(Expr::Var(var.clone()), lo, hi));
        }
        locals.insert(local, Expr::Var(var));
    }

    // Parameter names from the debug info, so contracts can refer to them.
    let mut names = Vec::new();
    for info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &info.value {
            let index = place.local.index();
            if place.projection.is_empty() && (1..=body.arg_count).contains(&index) {
                names.push((info.name.to_string(), Expr::Var(format!("_{index}"))));
            }
        }
    }

    let mut requires_exprs = Vec::new();
    for text in &requires {
        let parsed = spec::parse(text, &borrow_names(&names))
            .map_err(|err| Unsupported(format!("requires `{text}`: {err}")))?;
        requires_exprs.push(parsed);
    }

    let mut translator = Translator {
        tcx,
        body,
        name,
        params,
        ranges,
        names,
        ensures,
        vcs: Vec::new(),
    };
    let state = State {
        locals,
        fields: HashMap::new(),
        path: requires_exprs,
        visited: Vec::new(),
    };
    translator.walk(BasicBlock::new(0), state)?;
    Ok(translator.vcs)
}

/// The `requires` and `ensures` conditions written on a function. They arrive as
/// doc markers, which the macro crate writes and survive to the compiler's
/// attribute table.
// `get_all_attrs` is deprecated in favour of an API that is not yet in the pinned
// nightly sources. The pinned toolchain keeps this stable.
#[allow(deprecated)]
fn contracts(tcx: TyCtxt<'_>, def_id: DefId) -> (Vec<String>, Vec<String>) {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    for attribute in tcx.get_all_attrs(def_id) {
        if let Attribute::Parsed(AttributeKind::DocComment { comment, .. }) = attribute {
            let text = comment.as_str();
            if let Some(rest) = text.strip_prefix(REQUIRES_MARKER) {
                requires.push(rest.trim().to_string());
            } else if let Some(rest) = text.strip_prefix(ENSURES_MARKER) {
                ensures.push(rest.trim().to_string());
            }
        }
    }
    (requires, ensures)
}

/// Marker prefixes for contracts in doc attributes.
pub const REQUIRES_MARKER: &str = "tpt-proof-requires:";
/// Marker prefix for postconditions.
pub const ENSURES_MARKER: &str = "tpt-proof-ensures:";

/// Splits `|binder| body` into the binder and the body. Without a leading
/// `|binder|`, the whole text is the body.
fn split_binder(text: &str) -> (Option<&str>, &str) {
    match text.strip_prefix('|').and_then(|rest| rest.split_once('|')) {
        Some((binder, body)) => (Some(binder.trim()), body.trim()),
        None => (None, text),
    }
}

fn borrow_names(names: &[(String, Expr)]) -> Vec<(&str, Expr)> {
    names
        .iter()
        .map(|(name, expr)| (name.as_str(), expr.clone()))
        .collect()
}

struct Translator<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    name: String,
    params: Vec<(String, Sort)>,
    ranges: Vec<Expr>,
    /// Parameter names and the variables they stand for.
    names: Vec<(String, Expr)>,
    /// Postconditions, checked at each return.
    ensures: Vec<String>,
    vcs: Vec<Vc>,
}

/// The symbolic state along one path.
#[derive(Clone)]
struct State {
    /// Whole-local values.
    locals: HashMap<Local, Expr>,
    /// Fields of tuple locals, such as the `(value, overflowed)` pair from an
    /// overflowing operation. Keyed by local and field index.
    fields: HashMap<(Local, usize), Expr>,
    /// Branch conditions that hold on this path.
    path: Vec<Expr>,
    /// Blocks on this path, to detect loops.
    visited: Vec<BasicBlock>,
}

impl<'tcx> Translator<'_, 'tcx> {
    fn walk(&mut self, block: BasicBlock, mut state: State) -> Result<(), Unsupported> {
        if state.visited.contains(&block) {
            return unsupported("loops are not supported yet");
        }
        state.visited.push(block);
        let data = &self.body.basic_blocks[block];
        for statement in &data.statements {
            match &statement.kind {
                StatementKind::Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    self.assign(place, rvalue, &mut state)?;
                }
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop => {}
                _ => return unsupported("unsupported statement"),
            }
        }
        let Some(terminator) = &data.terminator else {
            return unsupported("block without a terminator");
        };
        match &terminator.kind {
            TerminatorKind::Return => self.check_ensures(&state),
            TerminatorKind::Goto { target, .. } => self.walk(*target, state),
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                let value = self.operand(cond, &state)?;
                let holds = if *expected { value } else { not(value) };
                let label = format!("{}: assertion at bb{}", self.name, block.index());
                self.push_vc(label, &state, holds);
                self.walk(*target, state)
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty = self.operand_ty(discr)?;
                let scrutinee = self.operand(discr, &state)?;
                let mut tested = Vec::new();
                for (value, target) in targets.iter() {
                    let condition = if discr_ty.is_bool() {
                        if value == 0 {
                            not(scrutinee.clone())
                        } else {
                            scrutinee.clone()
                        }
                    } else {
                        eq(scrutinee.clone(), Expr::Int(bits_to_int(value, discr_ty)?))
                    };
                    tested.push(condition.clone());
                    let mut branch = state.clone();
                    branch.path.push(condition);
                    self.walk(target, branch)?;
                }
                let mut otherwise = state;
                otherwise
                    .path
                    .push(and_all(tested.into_iter().map(not).collect()));
                self.walk(targets.otherwise(), otherwise)
            }
            _ => unsupported(
                "unsupported terminator (calls, drops, and unwinding are not supported)",
            ),
        }
    }

    fn assign(
        &mut self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        state: &mut State,
    ) -> Result<(), Unsupported> {
        if !place.projection.is_empty() {
            return unsupported("assignments through projections are not supported");
        }
        match rvalue {
            Rvalue::Use(operand, _) => {
                let value = self.operand(operand, state)?;
                state.locals.insert(place.local, value);
                Ok(())
            }
            Rvalue::BinaryOp(op, operands) => {
                let (lhs, rhs) = &**operands;
                let lhs_ty = self.operand_ty(lhs)?;
                let a = self.operand(lhs, state)?;
                let b = self.operand(rhs, state)?;
                match op {
                    BinOp::Add | BinOp::AddUnchecked => {
                        state.locals.insert(place.local, add(a, b));
                    }
                    BinOp::Sub | BinOp::SubUnchecked => {
                        state.locals.insert(place.local, sub(a, b));
                    }
                    BinOp::AddWithOverflow | BinOp::SubWithOverflow => {
                        let raw = if matches!(op, BinOp::AddWithOverflow) {
                            add(a, b)
                        } else {
                            sub(a, b)
                        };
                        let overflowed = overflow_of(raw.clone(), lhs_ty)?;
                        state.fields.insert((place.local, 0), raw);
                        state.fields.insert((place.local, 1), overflowed);
                    }
                    BinOp::Lt => {
                        state.locals.insert(place.local, lt(a, b));
                    }
                    BinOp::Le => {
                        state.locals.insert(place.local, le(a, b));
                    }
                    BinOp::Gt => {
                        state.locals.insert(place.local, lt(b, a));
                    }
                    BinOp::Ge => {
                        state.locals.insert(place.local, le(b, a));
                    }
                    BinOp::Eq => {
                        state.locals.insert(place.local, eq(a, b));
                    }
                    BinOp::Ne => {
                        state.locals.insert(place.local, not(eq(a, b)));
                    }
                    other => return unsupported(format!("operator {other:?} is not supported")),
                }
                Ok(())
            }
            _ => unsupported("unsupported right-hand side"),
        }
    }

    fn operand(&self, operand: &Operand<'tcx>, state: &State) -> Result<Expr, Unsupported> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place(place, state),
            Operand::RuntimeChecks(_) => unsupported("runtime checks are not supported"),
            Operand::Constant(constant) => {
                let ty = constant.const_.ty();
                if ty.is_bool() {
                    match constant.const_.try_to_bool() {
                        Some(value) => Ok(Expr::Bool(value)),
                        None => unsupported("boolean constant could not be evaluated"),
                    }
                } else {
                    let typing_env = TypingEnv::fully_monomorphized();
                    let size = self
                        .tcx
                        .layout_of(typing_env.as_query_input(ty))
                        .map_err(|_| Unsupported("constant has no layout".to_string()))?
                        .size;
                    let bits = constant.const_.try_to_bits(size);
                    match bits {
                        Some(bits) => Ok(Expr::Int(bits_to_int(bits, ty)?)),
                        None => unsupported("integer constant could not be evaluated"),
                    }
                }
            }
        }
    }

    fn place(&self, place: &Place<'tcx>, state: &State) -> Result<Expr, Unsupported> {
        match place.projection.as_slice() {
            [] => state
                .locals
                .get(&place.local)
                .cloned()
                .map_or_else(|| unsupported("use of an uninitialized local"), Ok),
            [PlaceElem::Field(field, _)] => state
                .fields
                .get(&(place.local, field.index()))
                .cloned()
                .map_or_else(|| unsupported("use of an uninitialized field"), Ok),
            _ => unsupported("projections are not supported"),
        }
    }

    /// The type of an operand. Used to pick ranges and comparisons.
    fn operand_ty(&self, operand: &Operand<'tcx>) -> Result<Ty<'tcx>, Unsupported> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place_ty(place),
            Operand::Constant(constant) => Ok(constant.const_.ty()),
            Operand::RuntimeChecks(_) => unsupported("runtime checks are not supported"),
        }
    }

    fn place_ty(&self, place: &Place<'tcx>) -> Result<Ty<'tcx>, Unsupported> {
        let local_ty = self.body.local_decls[place.local].ty;
        match place.projection.as_slice() {
            [] => Ok(local_ty),
            [PlaceElem::Field(field, _)] => match local_ty.kind() {
                ty::Tuple(fields) => Ok(fields[field.index()]),
                _ => unsupported("field of a non-tuple"),
            },
            _ => unsupported("projections are not supported"),
        }
    }

    /// Records a VC: the goal must hold under the parameter ranges and the path.
    fn push_vc(&mut self, label: String, state: &State, goal: Expr) {
        let mut assumptions = self.ranges.clone();
        assumptions.extend(state.path.iter().cloned());
        self.vcs.push(Vc {
            name: label,
            vars: self.params.clone(),
            assumptions,
            goal,
        });
    }

    /// At a return, each postcondition becomes a VC. The result is the value of
    /// the return place, and the binder in `|result| ...` names the same value.
    fn check_ensures(&mut self, state: &State) -> Result<(), Unsupported> {
        let ensures = self.ensures.clone();
        for text in &ensures {
            let (binder, body) = split_binder(text);
            let Some(result) = state.locals.get(&Local::new(0)).cloned() else {
                return unsupported(format!(
                    "ensures `{text}`: the return value is not a supported value"
                ));
            };
            let goal = {
                let mut names = borrow_names(&self.names);
                names.push(("result", result.clone()));
                if let Some(binder) = binder {
                    names.push((binder, result));
                }
                spec::parse(body, &names)
                    .map_err(|err| Unsupported(format!("ensures `{text}`: {err}")))?
            };
            let label = format!("{}: ensures {text}", self.name);
            self.push_vc(label, state, goal);
        }
        Ok(())
    }
}

fn sort_of(ty: Ty<'_>) -> Result<Sort, Unsupported> {
    if ty.is_bool() {
        Ok(Sort::Bool)
    } else if int_range(ty)?.is_some() {
        Ok(Sort::Int)
    } else {
        unsupported(format!("parameter of type {ty} is not supported"))
    }
}

/// The inclusive range of an integer type, or `None` for other types.
fn int_range(ty: Ty<'_>) -> Result<Option<(i128, i128)>, Unsupported> {
    let range = match ty.kind() {
        ty::Uint(kind) => {
            let bits = match kind {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 | UintTy::Usize => 64,
                UintTy::U128 => return unsupported("128-bit integers are not supported"),
            };
            Some((0, (1i128 << bits) - 1))
        }
        ty::Int(kind) => {
            let bits = match kind {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 | IntTy::Isize => 64,
                IntTy::I128 => return unsupported("128-bit integers are not supported"),
            };
            Some((-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1))
        }
        _ => None,
    };
    Ok(range)
}

/// Reads constant bits as a signed or unsigned integer of type `ty`.
fn bits_to_int(bits: u128, ty: Ty<'_>) -> Result<i64, Unsupported> {
    let value = match ty.kind() {
        ty::Int(_) => {
            let (lo, _) = int_range(ty)?.expect("signed integers have a range");
            let width = (-lo).trailing_zeros() + 1;
            let shift = 128 - width;
            ((bits << shift) as i128) >> shift
        }
        _ => bits as i128,
    };
    i64::try_from(value).map_err(|_| Unsupported("integer constant is out of range".to_string()))
}

fn in_range(value: Expr, lo: i128, hi: i128) -> Expr {
    Expr::And(vec![
        le(int_expr(lo), value.clone()),
        le(value, int_expr(hi)),
    ])
}

/// The overflow flag for an arithmetic result: the result leaves the type's range.
fn overflow_of(result: Expr, ty: Ty<'_>) -> Result<Expr, Unsupported> {
    let (lo, hi) =
        int_range(ty)?.ok_or_else(|| Unsupported("overflow on a non-integer".to_string()))?;
    Ok(Expr::Or(vec![
        lt(result.clone(), int_expr(lo)),
        lt(int_expr(hi), result),
    ]))
}

/// A literal for `value`. Literals above `i64::MAX` are written as a sum, since the
/// VC language stores integers as `i64`.
fn int_expr(value: i128) -> Expr {
    match i64::try_from(value) {
        Ok(small) => Expr::Int(small),
        Err(_) => add(Expr::Int(i64::MAX), int_expr(value - i64::MAX as i128)),
    }
}

fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new(a), Box::new(b))
}

fn sub(a: Expr, b: Expr) -> Expr {
    Expr::Sub(Box::new(a), Box::new(b))
}

fn lt(a: Expr, b: Expr) -> Expr {
    Expr::Lt(Box::new(a), Box::new(b))
}

fn le(a: Expr, b: Expr) -> Expr {
    Expr::Le(Box::new(a), Box::new(b))
}

fn eq(a: Expr, b: Expr) -> Expr {
    Expr::Eq(Box::new(a), Box::new(b))
}

fn not(a: Expr) -> Expr {
    Expr::Not(Box::new(a))
}

fn and_all(items: Vec<Expr>) -> Expr {
    Expr::And(items)
}
