//! Translation of optimized MIR into verification conditions (SPEC.md §5).
//!
//! This covers a subset: functions whose parameters and locals are integers or
//! booleans, with straight-line code, `if`, loops with invariants, and returns.
//! Each `assert` in MIR becomes a VC, which is the same as an overflow check.
//! Calls, references, multiplication, and division are reported as unsupported.
//!
//! The walk is symbolic. Each path through the function carries a state that maps
//! MIR locals to expressions and a list of branch conditions. A VC is emitted for
//! every assertion, under the path conditions and the range of each integer
//! parameter. The VC is only as strong as this translation, and Z3 checks it.
//!
//! Loops are handled with the standard invariant rule. A loop header is a block
//! that a back-edge returns to. Its invariant, written with `#[invariant(line,
//! cond)]`, is checked on entry, and the locals the loop assigns are replaced by
//! fresh values. On each path into the loop body the invariant is assumed, and on
//! each back-edge it must hold again. The header is matched to its invariant by
//! its source line.

use std::collections::HashMap;
use std::fmt;

use rustc_attr_ir::{Attribute, AttributeKind};
use rustc_hir::def_id::DefId;
use rustc_index::Idx;
use rustc_middle::mir::{
    BasicBlock, BinOp, Body, BorrowKind, Local, Operand, Place, PlaceElem, Rvalue, StatementKind,
    TerminatorKind, VarDebugInfoContents,
};
use rustc_middle::ty::{self, IntTy, Ty, TyCtxt, TypingEnv, UintTy};
use rustc_span::DUMMY_SP;
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
    let contracts = contracts(tcx, def_id);

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
    for text in &contracts.requires {
        let parsed = spec::parse(text, &borrow_names(&names))
            .map_err(|err| Unsupported(format!("requires `{text}`: {err}")))?;
        requires_exprs.push(parsed);
    }

    let graph = Graph::new(body);
    let mut translator = Translator {
        tcx,
        body,
        name,
        params,
        ranges,
        names,
        ensures: contracts.ensures,
        invariants: contracts.invariants,
        graph,
        fresh: Vec::new(),
        vcs: Vec::new(),
    };
    let state = State {
        locals,
        fields: HashMap::new(),
        path: requires_exprs,
        visited: Vec::new(),
        loops: Vec::new(),
    };
    translator.walk(BasicBlock::new(0), state)?;
    Ok(translator.vcs)
}

/// The contracts written on a function, read from its doc markers.
struct Contracts {
    requires: Vec<String>,
    ensures: Vec<String>,
    /// Loop invariants as `(line, condition)`.
    invariants: Vec<(u32, String)>,
}

/// Reads the contract markers that the macro crate writes. They arrive as doc
/// attributes, which survive to the compiler's attribute table.
// `get_all_attrs` is deprecated in favour of an API that is not yet in the pinned
// nightly sources. The pinned toolchain keeps this stable.
#[allow(deprecated)]
fn contracts(tcx: TyCtxt<'_>, def_id: DefId) -> Contracts {
    let mut contracts = Contracts {
        requires: Vec::new(),
        ensures: Vec::new(),
        invariants: Vec::new(),
    };
    for attribute in tcx.get_all_attrs(def_id) {
        if let Attribute::Parsed(AttributeKind::DocComment { comment, .. }) = attribute {
            let text = comment.as_str();
            if let Some(rest) = text.strip_prefix(REQUIRES_MARKER) {
                contracts.requires.push(rest.trim().to_string());
            } else if let Some(rest) = text.strip_prefix(ENSURES_MARKER) {
                contracts.ensures.push(rest.trim().to_string());
            } else if let Some(rest) = text.strip_prefix(INVARIANT_MARKER) {
                if let Some((line, condition)) = rest.trim().split_once(':') {
                    if let Ok(line) = line.trim().parse::<u32>() {
                        contracts
                            .invariants
                            .push((line, condition.trim().to_string()));
                    }
                }
            }
        }
    }
    contracts
}

/// Marker prefixes for contracts in doc attributes.
pub const REQUIRES_MARKER: &str = "tpt-proof-requires:";
/// Marker prefix for postconditions.
pub const ENSURES_MARKER: &str = "tpt-proof-ensures:";
/// Marker prefix for loop invariants.
pub const INVARIANT_MARKER: &str = "tpt-proof-invariant:";

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

/// The control-flow graph of a body, with predecessors and dominators.
struct Graph {
    successors: Vec<Vec<usize>>,
    predecessors: Vec<Vec<usize>>,
    /// `dominates[b][a]` is true when block `a` dominates block `b`.
    dominates: Vec<Vec<bool>>,
    reachable: Vec<bool>,
}

impl Graph {
    fn new(body: &Body<'_>) -> Graph {
        let n = body.basic_blocks.len();
        let successors: Vec<Vec<usize>> = (0..n)
            .map(|b| {
                successors_of(body, BasicBlock::new(b))
                    .into_iter()
                    .map(|s| s.index())
                    .collect()
            })
            .collect();
        let mut predecessors = vec![Vec::new(); n];
        for (block, targets) in successors.iter().enumerate() {
            for &target in targets {
                predecessors[target].push(block);
            }
        }

        // Reachability from the entry block.
        let mut reachable = vec![false; n];
        let mut stack = vec![0];
        while let Some(block) = stack.pop() {
            if !reachable[block] {
                reachable[block] = true;
                stack.extend(successors[block].iter().copied());
            }
        }

        // Iterative dominators: a block is dominated by all its predecessors' dominators.
        let mut dominates = vec![vec![true; n]; n];
        dominates[0] = (0..n).map(|a| a == 0).collect();
        let mut changed = true;
        while changed {
            changed = false;
            for block in 1..n {
                if !reachable[block] {
                    continue;
                }
                let mut next = vec![true; n];
                for &pred in predecessors[block].iter().filter(|p| reachable[**p]) {
                    for (a, slot) in next.iter_mut().enumerate() {
                        *slot &= dominates[pred][a];
                    }
                }
                next[block] = true;
                if next != dominates[block] {
                    dominates[block] = next;
                    changed = true;
                }
            }
        }

        Graph {
            successors,
            predecessors,
            dominates,
            reachable,
        }
    }

    /// Loop headers: blocks that a back-edge returns to, with the back-edge sources.
    fn loop_headers(&self) -> Vec<(usize, Vec<usize>)> {
        let mut headers: Vec<(usize, Vec<usize>)> = Vec::new();
        for (source, targets) in self.successors.iter().enumerate() {
            if !self.reachable[source] {
                continue;
            }
            for &target in targets {
                if self.dominates[source][target] {
                    match headers.iter_mut().find(|(h, _)| *h == target) {
                        Some((_, sources)) => sources.push(source),
                        None => headers.push((target, vec![source])),
                    }
                }
            }
        }
        headers
    }

    /// The natural loop of a header: the header and every block that reaches a
    /// back-edge source without passing through the header.
    fn loop_body(&self, header: usize, sources: &[usize]) -> Vec<usize> {
        let mut body = vec![header];
        let mut stack: Vec<usize> = sources.to_vec();
        while let Some(block) = stack.pop() {
            if !body.contains(&block) {
                body.push(block);
                stack.extend(self.predecessors[block].iter().copied());
            }
        }
        body
    }
}

fn successors_of(body: &Body<'_>, block: BasicBlock) -> Vec<BasicBlock> {
    match body.basic_blocks[block]
        .terminator
        .as_ref()
        .map(|t| &t.kind)
    {
        Some(TerminatorKind::Goto { target, .. }) => vec![*target],
        Some(TerminatorKind::Assert { target, .. }) => vec![*target],
        Some(TerminatorKind::SwitchInt { targets, .. }) => targets.all_targets().to_vec(),
        _ => Vec::new(),
    }
}

struct Translator<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    name: String,
    params: Vec<(String, Sort)>,
    ranges: Vec<Expr>,
    /// Named locals that are parameters, with the variables they stand for.
    names: Vec<(String, Expr)>,
    /// Postconditions, checked at each return.
    ensures: Vec<String>,
    /// Loop invariants by source line.
    invariants: Vec<(u32, String)>,
    graph: Graph,
    /// Fresh variables introduced by havoc, declared in every VC.
    fresh: Vec<(String, Sort)>,
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
    /// Blocks on this path, to detect irreducible control flow.
    visited: Vec<BasicBlock>,
    /// Loop headers already entered on this path.
    loops: Vec<BasicBlock>,
}

impl<'tcx> Translator<'_, 'tcx> {
    fn walk(&mut self, block: BasicBlock, mut state: State) -> Result<(), Unsupported> {
        if state.loops.contains(&block) {
            // A back-edge to a header entered on this path: the invariant must hold again.
            let line = self.line_of(block);
            let invariant = self.invariant_expr(line, &state)?;
            self.push_vc(
                format!("{}: loop at line {line}: invariant is preserved", self.name),
                &state,
                invariant,
            );
            return Ok(());
        }
        if self
            .graph
            .loop_headers()
            .iter()
            .any(|(h, _)| *h == block.index())
        {
            self.enter_loop(block, &mut state)?;
        } else if state.visited.contains(&block) {
            return unsupported("irreducible control flow is not supported");
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
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let operands: Vec<Operand<'tcx>> =
                    args.iter().map(|arg| arg.node.clone()).collect();
                self.call(block, func, &operands, destination, *target, state)
            }
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

    /// Enters a loop for the first time on this path. The invariant must hold on
    /// entry. Then the locals the loop assigns become arbitrary values that satisfy
    /// the invariant, and the body is walked from there.
    fn enter_loop(&mut self, header: BasicBlock, state: &mut State) -> Result<(), Unsupported> {
        let line = self.line_of(header);
        let entry = self.invariant_expr(line, state)?;
        self.push_vc(
            format!(
                "{}: loop at line {line}: invariant holds on entry",
                self.name
            ),
            state,
            entry,
        );

        let (_, sources) = self
            .graph
            .loop_headers()
            .into_iter()
            .find(|(h, _)| *h == header.index())
            .expect("the header was found by the caller");
        let body_blocks = self.graph.loop_body(header.index(), &sources);
        for local in self.assigned_locals(&body_blocks) {
            let ty = self.body.local_decls[local].ty;
            if matches!(ty.kind(), ty::Tuple(_)) {
                // A checked-arithmetic temporary. Its fields are rewritten before
                // they are read, so forgetting them is enough.
                state.fields.retain(|(owner, _), _| *owner != local);
                continue;
            }
            let sort = sort_of(ty)?;
            let var = format!("__h{}", self.fresh.len() + 1);
            self.fresh.push((var.clone(), sort));
            if let Some((lo, hi)) = int_range(ty)? {
                state.path.push(in_range(Expr::Var(var.clone()), lo, hi));
            }
            state.locals.insert(local, Expr::Var(var));
            state.fields.retain(|(owner, _), _| *owner != local);
        }

        let invariant = self.invariant_expr(line, state)?;
        state.path.push(invariant);
        state.loops.push(header);
        Ok(())
    }

    /// Locals assigned by the given blocks, in index order.
    fn assigned_locals(&self, blocks: &[usize]) -> Vec<Local> {
        let mut locals = Vec::new();
        for &block in blocks {
            for statement in &self.body.basic_blocks[BasicBlock::new(block)].statements {
                if let StatementKind::Assign(assign) = &statement.kind {
                    let local = assign.0.local;
                    if !locals.contains(&local) {
                        locals.push(local);
                    }
                }
            }
        }
        locals.sort_by_key(|local| local.index());
        locals
    }

    /// The source line where a block's terminator starts. Used to match loop
    /// headers with their invariants.
    fn line_of(&self, block: BasicBlock) -> u32 {
        let span = self.body.basic_blocks[block]
            .terminator
            .as_ref()
            .map_or(DUMMY_SP, |t| t.source_info.span);
        let loc = self.tcx.sess.source_map().lookup_char_pos(span.lo());
        loc.line as u32
    }

    /// The invariant written for the loop starting on `line`, evaluated in `state`.
    fn invariant_expr(&self, line: u32, state: &State) -> Result<Expr, Unsupported> {
        let Some((_, text)) = self.invariants.iter().find(|(l, _)| *l == line) else {
            return unsupported(format!("loop at line {line} has no invariant"));
        };
        let names = self.state_names(state);
        spec::parse(text, &borrow_names(&names))
            .map_err(|err| Unsupported(format!("invariant at line {line} `{text}`: {err}")))
    }

    /// Names visible in a state: every named local that has a value, with the last
    /// declaration of a name taking precedence, then the parameters.
    fn state_names(&self, state: &State) -> Vec<(String, Expr)> {
        let mut names = Vec::new();
        for info in self.body.var_debug_info.iter().rev() {
            if let VarDebugInfoContents::Place(place) = &info.value {
                if place.projection.is_empty() {
                    if let Some(value) = state.locals.get(&place.local) {
                        names.push((info.name.to_string(), value.clone()));
                    }
                }
            }
        }
        names.extend(self.names.iter().cloned());
        names
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
                    BinOp::Mul | BinOp::MulUnchecked => {
                        state.locals.insert(place.local, mul(a, b));
                    }
                    BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow => {
                        let raw = match op {
                            BinOp::AddWithOverflow => add(a, b),
                            BinOp::SubWithOverflow => sub(a, b),
                            _ => mul(a, b),
                        };
                        let overflowed = overflow_of(raw.clone(), lhs_ty)?;
                        state.fields.insert((place.local, 0), raw);
                        state.fields.insert((place.local, 1), overflowed);
                    }
                    BinOp::Div | BinOp::Rem => {
                        let value = match (op, lhs_ty.kind()) {
                            (BinOp::Div, ty::Uint(_)) => Expr::Div(Box::new(a), Box::new(b)),
                            (BinOp::Rem, ty::Uint(_)) => Expr::Rem(Box::new(a), Box::new(b)),
                            (BinOp::Div, ty::Int(_)) => signed_div(a, b),
                            (BinOp::Rem, ty::Int(_)) => signed_rem(a, b),
                            _ => return unsupported("division on this type is not supported"),
                        };
                        state.locals.insert(place.local, value);
                    }
                    BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor if lhs_ty.is_bool() => {
                        let value = match op {
                            BinOp::BitAnd => and(a, b),
                            BinOp::BitOr => Expr::Or(vec![a, b]),
                            _ => not(eq(a, b)),
                        };
                        state.locals.insert(place.local, value);
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
            Rvalue::Ref(_, BorrowKind::Shared, borrowed) => {
                // A shared borrow of a scalar place has that place's value: rustc
                // guarantees the place is not changed while the borrow is live.
                let value = self.place(borrowed, state)?;
                state.locals.insert(place.local, value);
                Ok(())
            }
            Rvalue::Ref(..) => unsupported("mutable borrows are not supported"),
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
            // A shared reference is represented by its pointee, so reading through it
            // reads the same value.
            [] | [PlaceElem::Deref] => state
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
            [PlaceElem::Deref] => match local_ty.kind() {
                ty::Ref(_, pointee, _) => Ok(*pointee),
                _ => unsupported("dereference of a non-reference"),
            },
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
        let vars = self
            .params
            .iter()
            .chain(self.fresh.iter())
            .cloned()
            .collect();
        self.vcs.push(Vc {
            name: label,
            vars,
            assumptions,
            goal,
        });
    }

    /// A direct call to a function without generic parameters. The callee's
    /// `requires` must hold here, which is a VC. The result is a fresh value about
    /// which the callee's `ensures` are assumed, so the callee must be verified
    /// separately for that to hold. A callee with no contracts gives an unknown
    /// result.
    fn call(
        &mut self,
        block: BasicBlock,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: &Place<'tcx>,
        target: Option<BasicBlock>,
        mut state: State,
    ) -> Result<(), Unsupported> {
        if !destination.projection.is_empty() {
            return unsupported("calls into projections are not supported");
        }
        let ty::FnDef(callee, generic_args) = self.operand_ty(func)?.kind() else {
            return unsupported("indirect calls are not supported");
        };
        if !generic_args.skip_binder().is_empty() {
            return unsupported("calls to generic functions are not supported");
        }
        let callee = *callee;
        if !self.tcx.is_mir_available(callee) {
            return unsupported(format!(
                "`{}` has no MIR to read its parameters from",
                self.tcx.def_path_str(callee)
            ));
        }
        let callee_body = self.tcx.optimized_mir(callee);
        if args.len() != callee_body.arg_count {
            return unsupported("call arity does not match the callee");
        }

        let mut values = Vec::new();
        for arg in args {
            values.push(self.operand(arg, &state)?);
        }
        let names = param_names(callee_body, &values);
        let callee_name = self.tcx.def_path_str(callee);
        let contracts = contracts(self.tcx, callee);

        for text in &contracts.requires {
            let goal = instantiate(text, &names, &[])
                .map_err(|err| Unsupported(format!("callee `{callee_name}`: {err}")))?;
            let label = format!(
                "{}: call to {callee_name} at bb{}: precondition `{text}`",
                self.name,
                block.index()
            );
            self.push_vc(label, &state, goal);
        }

        let return_ty = callee_body.local_decls[Local::new(0)].ty;
        let sort = sort_of(return_ty)?;
        let var = format!("__c{}", self.fresh.len() + 1);
        self.fresh.push((var.clone(), sort));
        let result = Expr::Var(var);
        if let Some((lo, hi)) = int_range(return_ty)? {
            state.path.push(in_range(result.clone(), lo, hi));
        }
        for text in &contracts.ensures {
            let (binder, body) = split_binder(text);
            let mut extra = vec![("result", result.clone())];
            if let Some(binder) = binder {
                extra.push((binder, result.clone()));
            }
            let assumed = instantiate(body, &names, &extra)
                .map_err(|err| Unsupported(format!("callee `{callee_name}`: {err}")))?;
            state.path.push(assumed);
        }

        state.locals.insert(destination.local, result);
        match target {
            Some(next) => self.walk(next, state),
            None => Ok(()),
        }
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

/// The parameter names of a body, with each name bound to the value passed for it.
fn param_names(body: &Body<'_>, values: &[Expr]) -> Vec<(String, Expr)> {
    let mut names = Vec::new();
    for info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &info.value {
            let index = place.local.index();
            if place.projection.is_empty() && (1..=body.arg_count).contains(&index) {
                names.push((info.name.to_string(), values[index - 1].clone()));
            }
        }
    }
    names
}

/// Strips shared references. A `&T` has the value model of `T`, which is sound because
/// rustc's borrow checker rules out changes to a shared borrow's pointee. Mutable
/// references are not supported.
fn peel_shared<'tcx>(ty: Ty<'tcx>) -> Result<Ty<'tcx>, Unsupported> {
    match ty.kind() {
        ty::Ref(_, pointee, mutability) if !mutability.is_mut() => peel_shared(*pointee),
        ty::Ref(..) => unsupported("mutable references are not supported"),
        _ => Ok(ty),
    }
}

fn sort_of(ty: Ty<'_>) -> Result<Sort, Unsupported> {
    let ty = peel_shared(ty)?;
    if ty.is_bool() {
        Ok(Sort::Bool)
    } else if int_range(ty)?.is_some() {
        Ok(Sort::Int)
    } else {
        unsupported(format!("values of type {ty} are not supported"))
    }
}

/// The inclusive range of an integer type, or `None` for other types. A shared
/// reference has the range of its pointee.
fn int_range(ty: Ty<'_>) -> Result<Option<(i128, i128)>, Unsupported> {
    let ty = peel_shared(ty)?;
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

fn mul(a: Expr, b: Expr) -> Expr {
    Expr::Mul(Box::new(a), Box::new(b))
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

/// Parses a contract condition against named values, with extra names such as
/// `result` appended.
fn instantiate(
    text: &str,
    names: &[(String, Expr)],
    extra: &[(&str, Expr)],
) -> Result<Expr, String> {
    let mut all = borrow_names(names);
    all.extend(extra.iter().cloned());
    spec::parse(text, &all).map_err(|err| err.to_string())
}

fn ite(condition: Expr, then: Expr, otherwise: Expr) -> Expr {
    Expr::Ite(Box::new(condition), Box::new(then), Box::new(otherwise))
}

fn neg(a: Expr) -> Expr {
    sub(Expr::Int(0), a)
}

fn and(a: Expr, b: Expr) -> Expr {
    Expr::And(vec![a, b])
}

/// Rust's `a / b` for signed integers, which rounds toward zero. The solver's `div`
/// rounds differently for negative operands, so each sign case uses it only on
/// non-negative operands, where the two agree.
fn signed_div(a: Expr, b: Expr) -> Expr {
    let non_negative_divisor = lt(Expr::Int(0), b.clone());
    ite(
        le(Expr::Int(0), a.clone()),
        ite(
            non_negative_divisor.clone(),
            Expr::Div(Box::new(a.clone()), Box::new(b.clone())),
            neg(Expr::Div(Box::new(a.clone()), Box::new(neg(b.clone())))),
        ),
        ite(
            non_negative_divisor,
            neg(Expr::Div(Box::new(neg(a.clone())), Box::new(b.clone()))),
            Expr::Div(Box::new(neg(a)), Box::new(neg(b))),
        ),
    )
}

/// Rust's `a % b` for signed integers: the remainder takes the sign of the dividend.
fn signed_rem(a: Expr, b: Expr) -> Expr {
    let magnitude = ite(le(Expr::Int(0), b.clone()), b.clone(), neg(b));
    ite(
        le(Expr::Int(0), a.clone()),
        Expr::Rem(Box::new(a.clone()), Box::new(magnitude.clone())),
        neg(Expr::Rem(Box::new(neg(a)), Box::new(magnitude))),
    )
}
