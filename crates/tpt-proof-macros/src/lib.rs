//! Attribute macros for tpt-proof (SPEC.md §3, Layers 2 and 4).
//!
//! - `#[requires(cond)]` checks `cond` on entry. Repeat it for several conditions.
//! - `#[ensures(|result| cond)]` checks `cond` on the return value.
//! - `#[runtime_check(cond)]` is the same as `requires`. It matches the example in SPEC.md §3.
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
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::{
    parse2, parse_quote, Attribute, Block, Expr, ExprClosure, ItemFn, LitInt, Pat, ReturnType,
    Stmt, Token, Type,
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

/// Checks a condition on entry, as an alias of [`requires`]. SPEC.md §3 uses this name.
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
    let condition: Expr = parse2(args)?;
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
    let closure: ExprClosure = parse2(args)?;
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
    fn ensures_rejects_a_closure_without_a_plain_binder() {
        let error = expand_ensures(
            "|a, b| a".parse().expect("tokens"),
            function("fn f(x: i32) -> i32 { x }"),
        );
        assert!(error.is_err());
    }
}
