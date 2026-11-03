//! A lemma library: a text file that holds a kernel environment and the lemmas
//! proved in it, so that another kernel can load them.
//!
//! The file is one declaration per line, as S-expressions:
//!
//! ```text
//! (sort "S")
//! (inductive "Nat" ("zero") ("succ" "Nat"))
//! (function "f" ("Ind") "Ind")
//! (predicate "P" ("Ind"))
//! (axiom "ax" (atom "A") "a justification")
//! (lemma "name" PROP PROOF)
//! ```
//!
//! The format is untrusted. [`load`] replays each declaration through the
//! kernel's own API, and each lemma goes through [`Kernel::check_proof`], so a
//! wrong or tampered file is rejected at the line that is wrong. [`save`] runs
//! that same load on its output before it returns the text.
//!
//! Limitations: definitions by recursion are saved as the defining axioms they
//! generate, and theorems that are not passed to [`save`] are not saved. A
//! lemma that uses one of them fails to load.

use std::collections::BTreeSet;
use std::fmt;

use tpt_proof_kernel::formula::Formula;
use tpt_proof_kernel::{Kernel, KernelError, ProofTerm, Prop, Sort, Term};

/// A theorem to save: its name, the claim, and the proof term that establishes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lemma {
    /// The theorem's name.
    pub name: String,
    /// The proposition proved.
    pub prop: Prop,
    /// The proof term.
    pub proof: ProofTerm,
}

/// Why a library could not be saved or loaded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LibraryError {
    /// The text is not well-formed S-expressions.
    Parse(String),
    /// A declaration or term is not a form the format defines.
    Malformed(String),
    /// The kernel rejected a declaration or lemma while it was loaded.
    Kernel {
        /// The declaration that failed, such as `lemma "name"`.
        declaration: String,
        /// The kernel's reason.
        error: KernelError,
    },
}

impl fmt::Display for LibraryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LibraryError::Parse(message) => write!(f, "library is not well-formed: {message}"),
            LibraryError::Malformed(message) => write!(f, "library is malformed: {message}"),
            LibraryError::Kernel { declaration, error } => {
                write!(f, "the kernel rejected {declaration}: {error}")
            }
        }
    }
}

impl std::error::Error for LibraryError {}

/// Writes the kernel's environment and the given lemmas as a library. The text
/// is loaded back before it is returned, so a library that does not replay is
/// never produced.
pub fn save(kernel: &Kernel, lemmas: &[Lemma]) -> Result<String, LibraryError> {
    let mut out = String::new();
    for line in environment(kernel) {
        out.push_str(&line);
        out.push('\n');
    }
    for lemma in lemmas {
        out.push_str(&format!(
            "(lemma {} {} {})\n",
            quote(&lemma.name),
            prop_text(&lemma.prop),
            proof_text(&lemma.proof)
        ));
    }
    load(&out)?;
    Ok(out)
}

/// Loads a library into a fresh kernel. Every declaration and lemma is checked
/// by the kernel, so the returned kernel holds only what it has accepted.
pub fn load(source: &str) -> Result<Kernel, LibraryError> {
    let mut kernel = Kernel::new();
    for declaration in read_all(source)? {
        let items = list(&declaration)?;
        let head = word(
            items
                .first()
                .ok_or_else(|| malformed("empty declaration"))?,
        )?;
        let label = format!("{head} {}", items.get(1).map_or(String::new(), label_of));
        let result = match head {
            "sort" => {
                fixed(items, 1, head)?;
                kernel.declare_sort(&text_at(items, 1)?).map(|_| ())
            }
            "inductive" => {
                let name = text_at(items, 1)?;
                let constructors = rest(items, 2)
                    .iter()
                    .map(constructor)
                    .collect::<Result<Vec<_>, _>>()?;
                let borrowed: Vec<(&str, Vec<Sort>)> = constructors
                    .iter()
                    .map(|(name, args)| (name.as_str(), args.clone()))
                    .collect();
                kernel.declare_inductive(&name, &borrowed).map(|_| ())
            }
            "function" => {
                fixed(items, 3, head)?;
                let args = sorts(&items[2])?;
                let result = Sort::named(&text(&items[3])?);
                kernel.declare_function_sorted(&text_at(items, 1)?, args, result)
            }
            "predicate" => {
                fixed(items, 2, head)?;
                kernel.declare_predicate_sorted(&text_at(items, 1)?, sorts(&items[2])?)
            }
            "axiom" => {
                fixed(items, 3, head)?;
                let prop = decode_prop(&items[2])?;
                let justification = text(&items[3])?;
                kernel.declare_axiom(&text_at(items, 1)?, prop, &justification)
            }
            "lemma" => {
                fixed(items, 3, head)?;
                let prop = decode_prop(&items[2])?;
                let proof = decode_proof(&items[3])?;
                kernel.declare_theorem(&text_at(items, 1)?, &proof, &prop)
            }
            other => return Err(malformed(&format!("unknown declaration `{other}`"))),
        };
        result.map_err(|error| LibraryError::Kernel {
            declaration: label.clone(),
            error,
        })?;
    }
    Ok(kernel)
}

/// The declarations for the kernel's sorts, inductive types, symbols, and axioms,
/// in an order that replays: every sort is declared before anything that uses it.
fn environment(kernel: &Kernel) -> Vec<String> {
    // The built-in integers are declared by every kernel, so they are not saved.
    let builtin = Kernel::new();
    let mut lines = Vec::new();
    let mut known: BTreeSet<String> = BTreeSet::from([Sort::ind().0]);
    let mut pending = Vec::new();
    for name in kernel.sorts() {
        match kernel.constructors(&Sort::named(name)) {
            Some(constructors) => pending.push((name.to_string(), constructors.to_vec())),
            None if name != Sort::ind().0 && !builtin.sorts().any(|sort| sort == name) => {
                known.insert(name.to_string());
                lines.push(format!("(sort {})", quote(name)));
            }
            None => {}
        }
    }
    // A constructor may only use sorts declared before it, so repeatedly emit
    // an inductive type whose argument sorts are all known.
    let mut constructor_names = BTreeSet::new();
    while !pending.is_empty() {
        let ready = pending.iter().position(|(name, constructors)| {
            constructors.iter().all(|(_, args)| {
                args.iter()
                    .all(|arg| arg.0 == *name || known.contains(&arg.0))
            })
        });
        // The kernel only admits arguments that are already declared, so this
        // always finds one. Guard anyway rather than loop forever.
        let Some(index) = ready else { break };
        let (name, constructors) = pending.remove(index);
        let rendered: Vec<String> = constructors
            .iter()
            .map(|(constructor, args)| {
                constructor_names.insert(constructor.clone());
                let mut fields = vec![quote(constructor)];
                fields.extend(args.iter().map(|arg| quote(&arg.0)));
                format!("({})", fields.join(" "))
            })
            .collect();
        lines.push(format!(
            "(inductive {} {})",
            quote(&name),
            rendered.join(" ")
        ));
        known.insert(name);
    }
    for (name, args, result) in kernel.functions() {
        // Constructors are declared with their inductive type, not on their own.
        if constructor_names.contains(name) || builtin.function_signature(name).is_some() {
            continue;
        }
        lines.push(format!(
            "(function {} {} {})",
            quote(name),
            sort_list(args),
            quote(&result.0)
        ));
    }
    for (name, args) in kernel.predicates() {
        if builtin.predicates().any(|(known, _)| known == name) {
            continue;
        }
        lines.push(format!("(predicate {} {})", quote(name), sort_list(args)));
    }
    for axiom in kernel.axioms() {
        lines.push(format!(
            "(axiom {} {} {})",
            quote(&axiom.name),
            prop_text(&axiom.prop),
            quote(&axiom.justification)
        ));
    }
    lines
}

fn sort_list(sorts: &[Sort]) -> String {
    let names: Vec<String> = sorts.iter().map(|sort| quote(&sort.0)).collect();
    format!("({})", names.join(" "))
}

fn quote(text: &str) -> String {
    let mut out = String::from("\"");
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

fn prop_text(prop: &Prop) -> String {
    match prop {
        Prop::Atom(name) => format!("(atom {})", quote(name)),
        Prop::Imp(a, b) => format!("(imp {} {})", prop_text(a), prop_text(b)),
        Prop::Forall(name, body) => format!("(forall {} {})", quote(name), prop_text(body)),
        Prop::ForallInd(name, sort, body) => {
            format!(
                "(all {} {} {})",
                quote(name),
                quote(&sort.0),
                prop_text(body)
            )
        }
        Prop::Eq(left, right) => format!("(eq {} {})", term_text(left), term_text(right)),
        Prop::Pred(symbol, args) => {
            let args: Vec<String> = args.iter().map(term_text).collect();
            format!("(pred {} {})", quote(symbol), args.join(" "))
        }
    }
}

fn term_text(term: &Term) -> String {
    match term {
        Term::Var(name) => format!("(var {})", quote(name)),
        Term::Fun(symbol, args) => {
            let args: Vec<String> = args.iter().map(term_text).collect();
            format!("(fun {} {})", quote(symbol), args.join(" "))
        }
    }
}

fn proof_text(term: &ProofTerm) -> String {
    match term {
        ProofTerm::Var(name) => format!("(hyp {})", quote(name)),
        ProofTerm::Const(name) => format!("(const {})", quote(name)),
        ProofTerm::Axiom(name) => format!("(axiom {})", quote(name)),
        ProofTerm::Lam(name, domain, body) => {
            format!(
                "(lam {} {} {})",
                quote(name),
                prop_text(domain),
                proof_text(body)
            )
        }
        ProofTerm::App(function, argument) => {
            format!("(app {} {})", proof_text(function), proof_text(argument))
        }
        ProofTerm::TyLam(name, body) => format!("(tylam {} {})", quote(name), proof_text(body)),
        ProofTerm::TyApp(function, argument) => {
            format!("(tyapp {} {})", proof_text(function), prop_text(argument))
        }
        ProofTerm::IndLam(name, sort, body) => {
            format!(
                "(indlam {} {} {})",
                quote(name),
                quote(&sort.0),
                proof_text(body)
            )
        }
        ProofTerm::IndApp(function, argument) => {
            format!("(indapp {} {})", proof_text(function), term_text(argument))
        }
        ProofTerm::Refl(term) => format!("(refl {})", term_text(term)),
        ProofTerm::Sym(proof) => format!("(sym {})", proof_text(proof)),
        ProofTerm::Trans(first, second) => {
            format!("(trans {} {})", proof_text(first), proof_text(second))
        }
        ProofTerm::Cong(symbol, args) => {
            let args: Vec<String> = args.iter().map(proof_text).collect();
            format!("(cong {} {})", quote(symbol), args.join(" "))
        }
        ProofTerm::Leibniz(name, motive, equation, proof) => format!(
            "(leibniz {} {} {} {})",
            quote(name),
            prop_text(motive),
            proof_text(equation),
            proof_text(proof)
        ),
        ProofTerm::Cases(name, sort, motive, cases) => {
            let cases: Vec<String> = cases.iter().map(proof_text).collect();
            format!(
                "(cases {} {} {} {})",
                quote(name),
                quote(&sort.0),
                prop_text(motive),
                cases.join(" ")
            )
        }
        ProofTerm::Induct(name, sort, motive, cases) => {
            let cases: Vec<String> = cases.iter().map(proof_text).collect();
            format!(
                "(induct {} {} {} {})",
                quote(name),
                quote(&sort.0),
                prop_text(motive),
                cases.join(" ")
            )
        }
        ProofTerm::Taut(formula) => format!("(taut {})", formula_text(formula)),
    }
}

fn formula_text(formula: &Formula) -> String {
    let parts = |items: &[Formula]| -> String {
        items.iter().map(formula_text).collect::<Vec<_>>().join(" ")
    };
    match formula {
        Formula::Atom(prop) => format!("(fatom {})", prop_text(prop)),
        Formula::Const(value) => format!("(fconst {value})"),
        Formula::Not(a) => format!("(fnot {})", formula_text(a)),
        Formula::And(items) => format!("(fand {})", parts(items)),
        Formula::Or(items) => format!("(for {})", parts(items)),
        Formula::Imp(a, b) => format!("(fimp {} {})", formula_text(a), formula_text(b)),
        Formula::Iff(a, b) => format!("(fiff {} {})", formula_text(a), formula_text(b)),
    }
}

/// A token of the library text.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Open,
    Close,
    Word(String),
    Text(String),
}

/// A parsed S-expression.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Sexp {
    /// A bare word, such as a form tag.
    Word(String),
    /// A quoted string, such as a name.
    Text(String),
    List(Vec<Sexp>),
}

fn tokenize(text: &str) -> Result<Vec<Token>, LibraryError> {
    let mut tokens = Vec::new();
    let mut chars = text.chars().peekable();
    while let Some(&ch) = chars.peek() {
        match ch {
            c if c.is_whitespace() => {
                chars.next();
            }
            '(' => {
                chars.next();
                tokens.push(Token::Open);
            }
            ')' => {
                chars.next();
                tokens.push(Token::Close);
            }
            '"' => {
                chars.next();
                let mut value = String::new();
                loop {
                    match chars.next() {
                        None => return Err(LibraryError::Parse("unterminated string".into())),
                        Some('"') => break,
                        Some('\\') => match chars.next() {
                            Some('\\') => value.push('\\'),
                            Some('"') => value.push('"'),
                            Some('n') => value.push('\n'),
                            _ => return Err(LibraryError::Parse("unknown escape".into())),
                        },
                        Some(other) => value.push(other),
                    }
                }
                tokens.push(Token::Text(value));
            }
            _ => {
                let mut word = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' || c == '"' {
                        break;
                    }
                    word.push(c);
                    chars.next();
                }
                tokens.push(Token::Word(word));
            }
        }
    }
    Ok(tokens)
}

/// Reads every top-level S-expression in the text.
fn read_all(text: &str) -> Result<Vec<Sexp>, LibraryError> {
    let tokens = tokenize(text)?;
    let mut position = 0;
    let mut out = Vec::new();
    while position < tokens.len() {
        out.push(read_one(&tokens, &mut position)?);
    }
    Ok(out)
}

fn read_one(tokens: &[Token], position: &mut usize) -> Result<Sexp, LibraryError> {
    let token = tokens
        .get(*position)
        .ok_or_else(|| LibraryError::Parse("unexpected end of text".into()))?;
    *position += 1;
    match token {
        Token::Open => {
            let mut items = Vec::new();
            loop {
                match tokens.get(*position) {
                    None => return Err(LibraryError::Parse("missing `)`".into())),
                    Some(Token::Close) => {
                        *position += 1;
                        return Ok(Sexp::List(items));
                    }
                    Some(_) => items.push(read_one(tokens, position)?),
                }
            }
        }
        Token::Close => Err(LibraryError::Parse("unexpected `)`".into())),
        Token::Word(word) => Ok(Sexp::Word(word.clone())),
        Token::Text(text) => Ok(Sexp::Text(text.clone())),
    }
}

fn malformed(message: &str) -> LibraryError {
    LibraryError::Malformed(message.to_string())
}

fn list(sexp: &Sexp) -> Result<&[Sexp], LibraryError> {
    match sexp {
        Sexp::List(items) => Ok(items),
        other => Err(malformed(&format!(
            "expected a list, found {}",
            label_of(other)
        ))),
    }
}

fn word(sexp: &Sexp) -> Result<&str, LibraryError> {
    match sexp {
        Sexp::Word(word) => Ok(word),
        other => Err(malformed(&format!(
            "expected a form tag, found {}",
            label_of(other)
        ))),
    }
}

fn text(sexp: &Sexp) -> Result<String, LibraryError> {
    match sexp {
        Sexp::Text(text) => Ok(text.clone()),
        other => Err(malformed(&format!(
            "expected a name, found {}",
            label_of(other)
        ))),
    }
}

fn text_at(items: &[Sexp], index: usize) -> Result<String, LibraryError> {
    text(
        items
            .get(index)
            .ok_or_else(|| malformed("missing a name"))?,
    )
}

/// Checks that a form has exactly `fields` arguments after its tag.
fn fixed(items: &[Sexp], fields: usize, head: &str) -> Result<(), LibraryError> {
    if items.len() == fields + 1 {
        Ok(())
    } else {
        Err(malformed(&format!("`{head}` takes {fields} field(s)")))
    }
}

fn label_of(sexp: &Sexp) -> String {
    match sexp {
        Sexp::Word(word) => word.clone(),
        Sexp::Text(text) => quote(text),
        Sexp::List(_) => "a list".to_string(),
    }
}

fn sorts(sexp: &Sexp) -> Result<Vec<Sort>, LibraryError> {
    list(sexp)?
        .iter()
        .map(|item| Ok(Sort::named(&text(item)?)))
        .collect()
}

fn constructor(sexp: &Sexp) -> Result<(String, Vec<Sort>), LibraryError> {
    let items = list(sexp)?;
    let name = text_at(items, 0)?;
    let args = rest(items, 1)
        .iter()
        .map(|item| Ok(Sort::named(&text(item)?)))
        .collect::<Result<Vec<_>, LibraryError>>()?;
    Ok((name, args))
}

fn decode_term(sexp: &Sexp) -> Result<Term, LibraryError> {
    let items = list(sexp)?;
    let head = word(items.first().ok_or_else(|| malformed("empty term"))?)?;
    match head {
        "var" => {
            fixed(items, 1, head)?;
            Ok(Term::var(&text_at(items, 1)?))
        }
        "fun" => {
            let args = rest(items, 2)
                .iter()
                .map(decode_term)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Term::app(&text_at(items, 1)?, args))
        }
        other => Err(malformed(&format!("unknown term `{other}`"))),
    }
}

fn decode_prop(sexp: &Sexp) -> Result<Prop, LibraryError> {
    let items = list(sexp)?;
    let head = word(
        items
            .first()
            .ok_or_else(|| malformed("empty proposition"))?,
    )?;
    match head {
        "atom" => {
            fixed(items, 1, head)?;
            Ok(Prop::atom(&text_at(items, 1)?))
        }
        "imp" => {
            fixed(items, 2, head)?;
            Ok(Prop::imp(decode_prop(&items[1])?, decode_prop(&items[2])?))
        }
        "forall" => {
            fixed(items, 2, head)?;
            Ok(Prop::forall(&text_at(items, 1)?, decode_prop(&items[2])?))
        }
        "all" => {
            fixed(items, 3, head)?;
            Ok(Prop::forall_sorted(
                &text_at(items, 1)?,
                Sort::named(&text_at(items, 2)?),
                decode_prop(&items[3])?,
            ))
        }
        "eq" => {
            fixed(items, 2, head)?;
            Ok(Prop::Eq(decode_term(&items[1])?, decode_term(&items[2])?))
        }
        "pred" => {
            let args = rest(items, 2)
                .iter()
                .map(decode_term)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Prop::Pred(text_at(items, 1)?, args))
        }
        other => Err(malformed(&format!("unknown proposition `{other}`"))),
    }
}

fn decode_proof(sexp: &Sexp) -> Result<ProofTerm, LibraryError> {
    let items = list(sexp)?;
    let head = word(items.first().ok_or_else(|| malformed("empty proof"))?)?;
    let boxed = |item: &Sexp| decode_proof(item).map(Box::new);
    match head {
        "hyp" => {
            fixed(items, 1, head)?;
            Ok(ProofTerm::Var(text_at(items, 1)?))
        }
        "const" => {
            fixed(items, 1, head)?;
            Ok(ProofTerm::Const(text_at(items, 1)?))
        }
        "axiom" => {
            fixed(items, 1, head)?;
            Ok(ProofTerm::Axiom(text_at(items, 1)?))
        }
        "lam" => {
            fixed(items, 3, head)?;
            Ok(ProofTerm::Lam(
                text_at(items, 1)?,
                decode_prop(&items[2])?,
                boxed(&items[3])?,
            ))
        }
        "app" => {
            fixed(items, 2, head)?;
            Ok(ProofTerm::App(boxed(&items[1])?, boxed(&items[2])?))
        }
        "tylam" => {
            fixed(items, 2, head)?;
            Ok(ProofTerm::TyLam(text_at(items, 1)?, boxed(&items[2])?))
        }
        "tyapp" => {
            fixed(items, 2, head)?;
            Ok(ProofTerm::TyApp(boxed(&items[1])?, decode_prop(&items[2])?))
        }
        "indlam" => {
            fixed(items, 3, head)?;
            Ok(ProofTerm::IndLam(
                text_at(items, 1)?,
                Sort::named(&text_at(items, 2)?),
                boxed(&items[3])?,
            ))
        }
        "indapp" => {
            fixed(items, 2, head)?;
            Ok(ProofTerm::IndApp(
                boxed(&items[1])?,
                decode_term(&items[2])?,
            ))
        }
        "refl" => {
            fixed(items, 1, head)?;
            Ok(ProofTerm::Refl(decode_term(&items[1])?))
        }
        "sym" => {
            fixed(items, 1, head)?;
            Ok(ProofTerm::Sym(boxed(&items[1])?))
        }
        "trans" => {
            fixed(items, 2, head)?;
            Ok(ProofTerm::Trans(boxed(&items[1])?, boxed(&items[2])?))
        }
        "cong" => {
            let args = rest(items, 2)
                .iter()
                .map(decode_proof)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ProofTerm::Cong(text_at(items, 1)?, args))
        }
        "leibniz" => {
            fixed(items, 4, head)?;
            Ok(ProofTerm::Leibniz(
                text_at(items, 1)?,
                decode_prop(&items[2])?,
                boxed(&items[3])?,
                boxed(&items[4])?,
            ))
        }
        "cases" | "induct" => {
            let cases = rest(items, 4)
                .iter()
                .map(decode_proof)
                .collect::<Result<Vec<_>, _>>()?;
            if items.len() < 4 {
                return Err(malformed(&format!(
                    "`{head}` takes a variable, a sort, and a motive"
                )));
            }
            let name = text_at(items, 1)?;
            let sort = Sort::named(&text_at(items, 2)?);
            let motive = decode_prop(&items[3])?;
            Ok(if head == "cases" {
                ProofTerm::Cases(name, sort, motive, cases)
            } else {
                ProofTerm::Induct(name, sort, motive, cases)
            })
        }
        "taut" => {
            fixed(items, 1, head)?;
            Ok(ProofTerm::Taut(decode_formula(&items[1])?))
        }
        other => Err(malformed(&format!("unknown proof form `{other}`"))),
    }
}

fn decode_formula(sexp: &Sexp) -> Result<Formula, LibraryError> {
    let items = list(sexp)?;
    let head = word(items.first().ok_or_else(|| malformed("empty formula"))?)?;
    let decode_all = |from: usize| -> Result<Vec<Formula>, LibraryError> {
        rest(items, from).iter().map(decode_formula).collect()
    };
    match head {
        "fatom" => {
            fixed(items, 1, head)?;
            Ok(Formula::Atom(decode_prop(&items[1])?))
        }
        "fconst" => {
            fixed(items, 1, head)?;
            match word(&items[1])? {
                "true" => Ok(Formula::Const(true)),
                "false" => Ok(Formula::Const(false)),
                other => Err(malformed(&format!("unknown constant `{other}`"))),
            }
        }
        "fnot" => {
            fixed(items, 1, head)?;
            Ok(Formula::Not(Box::new(decode_formula(&items[1])?)))
        }
        "fand" => Ok(Formula::And(decode_all(1)?)),
        "for" => Ok(Formula::Or(decode_all(1)?)),
        "fimp" => {
            fixed(items, 2, head)?;
            Ok(Formula::Imp(
                Box::new(decode_formula(&items[1])?),
                Box::new(decode_formula(&items[2])?),
            ))
        }
        "fiff" => {
            fixed(items, 2, head)?;
            Ok(Formula::Iff(
                Box::new(decode_formula(&items[1])?),
                Box::new(decode_formula(&items[2])?),
            ))
        }
        other => Err(malformed(&format!("unknown formula form `{other}`"))),
    }
}

/// The fields of a form after position `from`. Empty when the form is shorter,
/// so a malformed form reports a missing field instead of panicking.
fn rest(items: &[Sexp], from: usize) -> &[Sexp] {
    items.get(from..).unwrap_or(&[])
}
