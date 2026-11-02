//! Attribute macros for tpt-proof (spec.txt §3, Layers 2 and 4).
//!
//! - `#[requires(cond)]` checks `cond` on entry. Repeat it for several conditions.
//! - `#[ensures(|result| cond)]` checks `cond` on the return value.
//! - `#[runtime_check(cond)]` is the same as `requires`. It matches the example in spec.txt §3.
//!
//! Each contract does two things. It records itself as a doc marker, which the
//! MIR translator reads (see `tpt-proof-mir`). It also compiles to a runtime check:
//! a `debug_assert!`, which costs nothing in release builds. The runtime check is
//! switched off by `cfg(tpt_proof_verify)`, which the verification driver sets, so
//! the translator sees only the function's own code.
//!
//! `ensures` evaluates the body inside a closure, so `return` and `?` work as
//! usual. Since a closure is used, the function must declare its return type
//! explicitly, which is always true for a non-unit return.
//!
//! Crates that use these attributes declare the cfg, so the compiler does not warn
//! about it:
//!
//! ```text
//! [lints.rust]
//! unexpected_cfgs = { level = "warn", check-cfg = ["cfg(tpt_proof_verify)"] }
//! ```

use proc_macro::TokenStream;
use proc_macro2::{Spacing, TokenStream as TokenStream2, TokenTree};
use quote::{format_ident, quote, ToTokens};
use syn::parse::{Parse, ParseStream, Parser};
use syn::punctuated::Punctuated;
use syn::{
    parse2, parse_quote, Attribute, BinOp, Block, Expr, ExprBinary, ExprClosure, ExprLit, Field,
    Fields, Ident, ItemFn, ItemStruct, Lit, LitInt, Pat, ReturnType, Stmt, Token, Type,
};

/// Doc marker prefix for preconditions. Must match `tpt-proof-mir`.
const REQUIRES_MARKER: &str = "tpt-proof-requires:";
/// Doc marker prefix for postconditions. Must match `tpt-proof-mir`.
const ENSURES_MARKER: &str = "tpt-proof-ensures:";
/// Doc marker prefix for loop invariants. Must match `tpt-proof-mir`.
const INVARIANT_MARKER: &str = "tpt-proof-invariant:";

/// Declares the invariant of the loop that starts on source line `line`.
///
/// ```text
/// #[invariant(4, i <= n && total == i)]
/// fn sum(n: u32) -> u32 { /* a while loop starting on line 4 */ }
/// ```
///
/// The invariant is a verification condition only. It has no runtime check,
/// because a loop body is not rewritten.
#[proc_macro_attribute]
pub fn invariant(args: TokenStream, item: TokenStream) -> TokenStream {
    into_output(expand_invariant(args.into(), item.into()))
}

/// The arguments of `#[invariant(line, condition)]`.
struct InvariantArgs {
    line: LitInt,
    condition: Expr,
}

impl Parse for InvariantArgs {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let line = input.parse()?;
        input.parse::<Token![,]>()?;
        let condition = input.parse()?;
        Ok(InvariantArgs { line, condition })
    }
}

fn expand_invariant(args: TokenStream2, item: TokenStream2) -> syn::Result<TokenStream2> {
    // The line number comes first, so only the condition after its comma may use `==>`.
    let head = punct_positions(&args, ',')
        .first()
        .map_or(0, |comma| comma + 1);
    let args = desugar_after(args, head);
    let args: InvariantArgs = parse2(args)?;
    let mut function: ItemFn = parse2(item)?;
    let line: u32 = args.line.base10_parse()?;
    let text = args.condition.to_token_stream().to_string();
    function
        .attrs
        .push(marker(INVARIANT_MARKER, &format!("{line}: {text}")));
    Ok(quote!(#function))
}

/// Checks a precondition on entry to the function.
///
/// ```text
/// #[requires(divisor != 0)]
/// fn divide(value: u32, divisor: u32) -> u32 { value / divisor }
/// ```
#[proc_macro_attribute]
pub fn requires(args: TokenStream, item: TokenStream) -> TokenStream {
    into_output(expand_entry(
        args.into(),
        item.into(),
        "precondition failed",
        REQUIRES_MARKER,
    ))
}

/// Checks a condition on entry, as an alias of [`requires`]. spec.txt §3 uses this name.
#[proc_macro_attribute]
pub fn runtime_check(args: TokenStream, item: TokenStream) -> TokenStream {
    into_output(expand_entry(
        args.into(),
        item.into(),
        "runtime check failed",
        REQUIRES_MARKER,
    ))
}

/// Checks a postcondition on the return value. The binder names the result.
///
/// ```text
/// #[ensures(|result| *result >= 0)]
/// fn abs(x: i32) -> i32 { if x < 0 { -x } else { x } }
/// ```
#[proc_macro_attribute]
pub fn ensures(args: TokenStream, item: TokenStream) -> TokenStream {
    into_output(expand_ensures(args.into(), item.into()))
}

/// Layer 1: a struct whose field is always below a bound.
///
/// The bound is another field or an integer literal. The macro adds a checked
/// constructor, `new`, which takes every field in declaration order and returns
/// `None` when the predicate fails, and a getter for the refined field:
///
/// ```text
/// #[refined(value < total_blocks)]
/// struct BlockIndex { value: usize, total_blocks: usize }
///
/// BlockIndex::new(3, 8)  // Some
/// BlockIndex::new(8, 8)  // None
/// ```
///
/// The refined field must be `Copy`, because the getter returns it by value. A
/// struct literal in the defining module can still skip `new`, so keep the
/// struct in its own module when the bound must hold everywhere.
#[proc_macro_attribute]
pub fn refined(args: TokenStream, item: TokenStream) -> TokenStream {
    into_output(expand_refined(args.into(), item.into()))
}

/// The bound of a refined struct: the name of another field, or a literal.
enum Bound {
    Field(Ident),
    Literal(LitInt),
}

fn expand_refined(args: TokenStream2, item: TokenStream2) -> syn::Result<TokenStream2> {
    let predicate: Expr = parse2(args)?;
    let item: ItemStruct = parse2(item)?;
    let Expr::Binary(ExprBinary {
        left,
        op: BinOp::Lt(_),
        right,
        ..
    }) = &predicate
    else {
        return Err(syn::Error::new_spanned(
            &predicate,
            "`refined` takes a predicate of the form `field < bound`",
        ));
    };
    let value = field_name(left)?;
    let bound = match &**right {
        Expr::Path(_) => Bound::Field(field_name(right)?),
        Expr::Lit(ExprLit {
            lit: Lit::Int(literal),
            ..
        }) => Bound::Literal(literal.clone()),
        other => {
            return Err(syn::Error::new_spanned(
                other,
                "the bound must be a field name or an integer literal",
            ))
        }
    };

    let fields = named_fields(&item)?;
    let has_field = |name: &Ident| fields.iter().any(|f| f.ident.as_ref() == Some(name));
    let value_type = match fields.iter().find(|f| f.ident.as_ref() == Some(&value)) {
        Some(field) => &field.ty,
        None => {
            return Err(syn::Error::new_spanned(
                &value,
                "`refined` names a field that the struct does not have",
            ))
        }
    };
    let check: Expr = match &bound {
        Bound::Field(name) => {
            if !has_field(name) {
                return Err(syn::Error::new_spanned(
                    name,
                    "`refined` names a bound field that the struct does not have",
                ));
            }
            parse_quote!(#value < #name)
        }
        Bound::Literal(literal) => parse_quote!(#value < #literal),
    };

    let name = &item.ident;
    let names: Vec<&Ident> = fields.iter().filter_map(|f| f.ident.as_ref()).collect();
    let types: Vec<&Type> = fields.iter().map(|f| &f.ty).collect();
    let doc = format!(
        "Builds the value, or returns `None` when `{}` does not hold.",
        predicate.to_token_stream()
    );
    Ok(quote! {
        #item

        impl #name {
            #[doc = #doc]
            pub fn new(#(#names: #types),*) -> ::core::option::Option<Self> {
                if #check {
                    ::core::option::Option::Some(Self { #(#names),* })
                } else {
                    ::core::option::Option::None
                }
            }

            /// The refined field. It always satisfies the predicate.
            pub fn #value(&self) -> #value_type {
                self.#value
            }
        }
    })
}

/// Layer 1: a type-state machine over a struct. spec.txt §3.
///
/// `#[state_machine(Idle, Busy)]` on `struct Worker { id: u32 }` declares one
/// marker type per listed state, makes the struct generic over its state, and
/// adds a `state: PhantomData<S>` field. The state trait is sealed, so only the
/// listed states implement it. Transitions are written by hand in the defining
/// module, and they move the value with `self.transition()`:
///
/// ```text
/// impl Worker<Idle> {
///     fn begin(self) -> Worker<Busy> { self.transition() }
/// }
/// ```
///
/// The struct must not already have a `state` field, and it cannot have generics.
#[proc_macro_attribute]
pub fn state_machine(args: TokenStream, item: TokenStream) -> TokenStream {
    into_output(expand_state_machine(args.into(), item.into()))
}

fn expand_state_machine(args: TokenStream2, item: TokenStream2) -> syn::Result<TokenStream2> {
    let states: Vec<Ident> = Punctuated::<Ident, Token![,]>::parse_terminated
        .parse2(args)?
        .into_iter()
        .collect();
    if states.is_empty() {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            "`state_machine` needs at least one state name",
        ));
    }
    for (index, state) in states.iter().enumerate() {
        if states[..index].contains(state) {
            return Err(syn::Error::new_spanned(
                state,
                "this state is listed more than once",
            ));
        }
    }

    let mut item: ItemStruct = parse2(item)?;
    let fields = named_fields(&item)?;
    if fields
        .iter()
        .any(|f| f.ident.as_ref().is_some_and(|i| i == "state"))
    {
        return Err(syn::Error::new_spanned(
            &item.ident,
            "`state_machine` adds a `state` field; remove it from the struct",
        ));
    }
    let names: Vec<Ident> = fields.iter().filter_map(|f| f.ident.clone()).collect();

    let name = item.ident.clone();
    let vis = item.vis.clone();
    let state_trait = format_ident!("{}State", name);
    let sealed = format_ident!("__tpt_sealed_{}", name);

    item.generics = parse_quote!(<S: #state_trait>);
    if let Fields::Named(named) = &mut item.fields {
        named.named.push(Field::parse_named.parse2(quote!(
            state: ::core::marker::PhantomData<S>
        ))?);
    }

    Ok(quote! {
        #[allow(non_snake_case)]
        mod #sealed {
            pub trait Sealed {}
        }

        /// A state of the machine. Only the states the macro declares implement it.
        #vis trait #state_trait: #sealed::Sealed {}

        #(
            #[doc = "A state of the machine."]
            #[derive(Debug, Clone, Copy, PartialEq, Eq)]
            #vis struct #states;
            impl #sealed::Sealed for #states {}
            impl #state_trait for #states {}
        )*

        #item

        impl<S: #state_trait> #name<S> {
            /// Moves the value to state `T`. The fields are kept, so only the type changes.
            fn transition<T: #state_trait>(self) -> #name<T> {
                #name {
                    #(#names: self.#names,)*
                    state: ::core::marker::PhantomData,
                }
            }
        }
    })
}

/// The named fields of a struct with no generics. Other shapes are rejected.
fn named_fields(item: &ItemStruct) -> syn::Result<Vec<&Field>> {
    if !item.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &item.generics,
            "generic structs are not supported by this attribute yet",
        ));
    }
    match &item.fields {
        Fields::Named(named) => Ok(named.named.iter().collect()),
        other => Err(syn::Error::new_spanned(
            other,
            "this attribute needs a struct with named fields",
        )),
    }
}

/// A single-segment path, read as a field name.
fn field_name(expr: &Expr) -> syn::Result<Ident> {
    match expr {
        Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
            Ok(path.path.segments[0].ident.clone())
        }
        _ => Err(syn::Error::new_spanned(expr, "expected a field name")),
    }
}

/// Rewrites `a ==> b` to `!(a) || (b)`. The implication operator binds loosest
/// and is right-associative, so `a ==> b ==> c` is `a ==> (b ==> c)`. Groups are
/// atomic, so only top-level occurrences are split.
fn desugar_implies(tokens: TokenStream2) -> TokenStream2 {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();
    match (0..trees.len()).find(|&i| is_implies_at(&trees, i)) {
        None => trees.into_iter().collect(),
        Some(arrow) => {
            let lhs: TokenStream2 = trees[..arrow].iter().cloned().collect();
            let rhs = desugar_implies(trees[arrow + 3..].iter().cloned().collect());
            quote!(!(#lhs) || (#rhs))
        }
    }
}

/// Whether `==>` starts at `index`. Rust lexes it as three joined puncts.
fn is_implies_at(trees: &[TokenTree], index: usize) -> bool {
    match trees.get(index..index + 3) {
        Some([TokenTree::Punct(a), TokenTree::Punct(b), TokenTree::Punct(c)]) => {
            a.as_char() == '='
                && b.as_char() == '='
                && c.as_char() == '>'
                && a.spacing() == Spacing::Joint
                && b.spacing() == Spacing::Joint
        }
        _ => false,
    }
}

/// Applies [`desugar_implies`] to the tokens after the first `head` token trees.
fn desugar_after(tokens: TokenStream2, head: usize) -> TokenStream2 {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();
    let head = head.min(trees.len());
    let head_tokens: TokenStream2 = trees[..head].iter().cloned().collect();
    let tail = desugar_implies(trees[head..].iter().cloned().collect());
    quote!(#head_tokens #tail)
}

/// The positions of the top-level punctuation `ch` in `tokens`.
fn punct_positions(tokens: &TokenStream2, ch: char) -> Vec<usize> {
    tokens
        .clone()
        .into_iter()
        .enumerate()
        .filter(|(_, tree)| matches!(tree, TokenTree::Punct(p) if p.as_char() == ch))
        .map(|(index, _)| index)
        .collect()
}

fn into_output(result: syn::Result<TokenStream2>) -> TokenStream {
    match result {
        Ok(tokens) => tokens.into(),
        Err(error) => error.to_compile_error().into(),
    }
}

/// The attribute that marks a contract for the translator.
fn marker(prefix: &str, text: &str) -> Attribute {
    let value = format!("{prefix} {text}");
    parse_quote!(#[doc = #value])
}

/// Expands `requires` and `runtime_check`: a debug check on entry, and a marker.
fn expand_entry(
    args: TokenStream2,
    item: TokenStream2,
    label: &str,
    prefix: &str,
) -> syn::Result<TokenStream2> {
    let condition: Expr = parse2(desugar_implies(args))?;
    let mut function: ItemFn = parse2(item)?;
    let text = condition.to_token_stream().to_string();
    let check: Stmt = parse_quote! {
        #[cfg(not(tpt_proof_verify))]
        debug_assert!(#condition, "{}: {}", #label, #text);
    };
    function.attrs.push(marker(prefix, &text));
    function.block.stmts.insert(0, check);
    Ok(quote!(#function))
}

/// Expands `ensures`: a debug check on the result, and a marker. The verification
/// build gets the body unchanged.
fn expand_ensures(args: TokenStream2, item: TokenStream2) -> syn::Result<TokenStream2> {
    // The binder is `|name|`, so only the body after the second `|` may use `==>`.
    let bars = punct_positions(&args, '|');
    let head = bars.get(1).map_or(0, |second| second + 1);
    let closure: ExprClosure = parse2(desugar_after(args, head))?;
    let mut function: ItemFn = parse2(item)?;

    let binder = match closure.inputs.first() {
        Some(Pat::Ident(ident)) if closure.inputs.len() == 1 => ident.ident.clone(),
        _ => {
            return Err(syn::Error::new_spanned(
                &closure.inputs,
                "`ensures` takes a closure with one plain name, such as `|result| ...`",
            ))
        }
    };
    let condition = *closure.body;
    let text = condition.to_token_stream().to_string();
    let return_type: Type = match &function.sig.output {
        ReturnType::Default => parse_quote!(()),
        ReturnType::Type(_, ty) => (**ty).clone(),
    };
    let body: Block = (*function.block).clone();

    let wrapped: Block = parse_quote! {{
        #[cfg(not(tpt_proof_verify))]
        {
            let __tpt_result: #return_type = (|| -> #return_type #body)();
            {
                let #binder = &__tpt_result;
                debug_assert!(#condition, "postcondition failed: {}", #text);
            }
            return __tpt_result;
        }
        #[cfg(tpt_proof_verify)]
        {
            return #body;
        }
    }};
    function
        .attrs
        .push(marker(ENSURES_MARKER, &format!("|{binder}| {text}")));
    *function.block = wrapped;
    Ok(quote!(#function))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn function(source: &str) -> TokenStream2 {
        source.parse().expect("valid tokens")
    }

    #[test]
    fn requires_records_a_marker_and_a_runtime_check() {
        let expanded = expand_entry(
            "x < 100".parse().expect("tokens"),
            function("fn f(x: u8) -> u8 { x }"),
            "precondition failed",
            REQUIRES_MARKER,
        )
        .expect("expands")
        .to_string();
        assert!(expanded.contains("tpt-proof-requires"), "{expanded}");
        assert!(expanded.contains("not (tpt_proof_verify)"), "{expanded}");
        assert!(expanded.contains("debug_assert"), "{expanded}");
    }

    #[test]
    fn ensures_records_the_binder_and_keeps_the_body_for_verification() {
        let expanded = expand_ensures(
            "|result| *result >= 0".parse().expect("tokens"),
            function("fn f(x: i32) -> i32 { x }"),
        )
        .expect("expands")
        .to_string();
        assert!(expanded.contains("tpt-proof-ensures"), "{expanded}");
        assert!(expanded.contains("tpt_proof_verify"), "{expanded}");
        assert!(expanded.contains("__tpt_result"), "{expanded}");
    }

    #[test]
    fn invariant_records_its_line_and_condition() {
        let expanded = expand_invariant(
            "4, i <= n".parse().expect("tokens"),
            function("fn sum(n: u32) -> u32 { n }"),
        )
        .expect("expands")
        .to_string();
        assert!(expanded.contains("tpt-proof-invariant"), "{expanded}");
        assert!(
            expanded.contains("tpt-proof-invariant: 4: i <= n"),
            "{expanded}"
        );
    }

    #[test]
    fn invariant_needs_a_line_and_a_condition() {
        let function = function("fn sum(n: u32) -> u32 { n }");
        assert!(expand_invariant("i <= n".parse().expect("tokens"), function.clone()).is_err());
        assert!(expand_invariant("4".parse().expect("tokens"), function).is_err());
    }

    #[test]
    fn refined_builds_a_checked_constructor_for_a_field_bound() {
        let expanded = expand_refined(
            "value < total".parse().expect("tokens"),
            function("struct Block { value: usize, total: usize }"),
        )
        .expect("expands")
        .to_string();
        assert!(
            expanded.contains("fn new (value : usize , total : usize)"),
            "{expanded}"
        );
        assert!(expanded.contains("if value < total"), "{expanded}");
        assert!(expanded.contains("fn value (& self)"), "{expanded}");
    }

    #[test]
    fn refined_accepts_a_literal_bound() {
        let expanded = expand_refined(
            "value < 8".parse().expect("tokens"),
            function("struct Slot { value: u8 }"),
        )
        .expect("expands")
        .to_string();
        assert!(expanded.contains("if value < 8"), "{expanded}");
    }

    #[test]
    fn refined_rejects_other_predicates_and_unknown_fields() {
        let item = || function("struct Block { value: usize, total: usize }");
        assert!(expand_refined("value <= total".parse().expect("tokens"), item()).is_err());
        assert!(expand_refined("missing < total".parse().expect("tokens"), item()).is_err());
        assert!(expand_refined("value < missing".parse().expect("tokens"), item()).is_err());
        assert!(expand_refined(
            "value < total".parse().expect("tokens"),
            function("enum Block { Value }")
        )
        .is_err());
    }

    #[test]
    fn state_machine_declares_states_and_a_sealed_trait() {
        let expanded = expand_state_machine(
            "Idle, Busy".parse().expect("tokens"),
            function("struct Worker { id: u32 }"),
        )
        .expect("expands")
        .to_string();
        assert!(expanded.contains("trait WorkerState"), "{expanded}");
        assert!(expanded.contains("struct Idle"), "{expanded}");
        assert!(expanded.contains("struct Busy"), "{expanded}");
        assert!(expanded.contains("PhantomData < S >"), "{expanded}");
        assert!(expanded.contains("fn transition"), "{expanded}");
    }

    #[test]
    fn state_machine_rejects_bad_state_lists() {
        let item = || function("struct Worker { id: u32 }");
        assert!(expand_state_machine("".parse().expect("tokens"), item()).is_err());
        assert!(expand_state_machine("Idle, Idle".parse().expect("tokens"), item()).is_err());
        assert!(expand_state_machine(
            "Idle".parse().expect("tokens"),
            function("struct Worker { state: u32 }")
        )
        .is_err());
    }

    #[test]
    fn ensures_rejects_a_closure_without_a_plain_binder() {
        let error = expand_ensures(
            "|a, b| a".parse().expect("tokens"),
            function("fn f(x: i32) -> i32 { x }"),
        );
        assert!(error.is_err());
    }
}

#[cfg(test)]
mod implication_tests {
    use super::*;

    fn desugared(source: &str) -> String {
        desugar_implies(source.parse().expect("tokens")).to_string()
    }

    #[test]
    fn implication_becomes_not_or() {
        assert_eq!(desugared("a ==> b"), "! (a) || (b)");
    }

    #[test]
    fn implication_is_right_associative() {
        assert_eq!(desugared("a ==> b ==> c"), "! (a) || (! (b) || (c))");
    }

    #[test]
    fn implication_binds_looser_than_connectives() {
        assert_eq!(
            desugared("x > 0 && y ==> z || w"),
            "! (x > 0 && y) || (z || w)"
        );
    }

    #[test]
    fn text_without_an_arrow_is_unchanged() {
        assert_eq!(desugared("x >= 0 && y != 1"), "x >= 0 && y != 1");
    }

    #[test]
    fn groups_hide_their_arrows() {
        assert_eq!(desugared("f(a ==> b)"), "f (a ==> b)");
    }

    #[test]
    fn invariant_skips_the_line_number() {
        let expanded = expand_invariant(
            "4, i <= n ==> total == i".parse().expect("tokens"),
            "fn sum(n: u32) -> u32 { n }".parse().expect("tokens"),
        )
        .expect("expands")
        .to_string();
        assert!(expanded.contains("tpt-proof-invariant"), "{expanded}");
        assert!(expanded.contains("! (i <= n)"), "{expanded}");
    }

    #[test]
    fn ensures_desugars_only_the_body() {
        let expanded = expand_ensures(
            "|result| *result >= 0 ==> *result < 10"
                .parse()
                .expect("tokens"),
            "fn f(x: i32) -> i32 { x }".parse().expect("tokens"),
        )
        .expect("expands")
        .to_string();
        assert!(
            expanded.contains("! (* result >= 0) || (* result < 10)"),
            "{expanded}"
        );
    }
}
