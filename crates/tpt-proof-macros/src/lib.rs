//! Attribute macros for tpt-proof (SPEC.md §3, Layers 2 and 4).
//!
//! These attributes compile specifications into debug-build checks. They are the
//! runtime side of the contract syntax. Each check is a `debug_assert!`, so it
//! costs nothing in release builds.
//!
//! - `#[requires(cond)]` checks `cond` on entry. Repeat it for several conditions.
//! - `#[ensures(|result| cond)]` checks `cond` on the return value.
//! - `#[runtime_check(cond)]` is the same as `requires`. It matches the example in SPEC.md §3.
//!
//! `ensures` evaluates the body inside a closure, so `return` and `?` work as
//! usual. Since a closure is used, the function must declare its return type
//! explicitly, which is always true for a non-unit return.

use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{
    parse_macro_input, parse_quote, Block, Expr, ExprClosure, ItemFn, Pat, ReturnType, Type,
};

/// Checks a precondition on entry to the function.
///
/// ```text
/// #[requires(divisor != 0)]
/// fn divide(value: u32, divisor: u32) -> u32 { value / divisor }
/// ```
#[proc_macro_attribute]
pub fn requires(args: TokenStream, item: TokenStream) -> TokenStream {
    let condition = parse_macro_input!(args as Expr);
    let function = parse_macro_input!(item as ItemFn);
    entry_check(condition, function, "precondition failed")
}

/// Checks a condition on entry, as an alias of [`requires`]. SPEC.md §3 uses this name.
#[proc_macro_attribute]
pub fn runtime_check(args: TokenStream, item: TokenStream) -> TokenStream {
    let condition = parse_macro_input!(args as Expr);
    let function = parse_macro_input!(item as ItemFn);
    entry_check(condition, function, "runtime check failed")
}

/// Checks a postcondition on the return value. The binder names the result.
///
/// ```text
/// #[ensures(|result| *result >= 0)]
/// fn abs(x: i32) -> i32 { if x < 0 { -x } else { x } }
/// ```
#[proc_macro_attribute]
pub fn ensures(args: TokenStream, item: TokenStream) -> TokenStream {
    let closure = parse_macro_input!(args as ExprClosure);
    let mut function = parse_macro_input!(item as ItemFn);

    let binder = match closure.inputs.first() {
        Some(Pat::Ident(ident)) if closure.inputs.len() == 1 => ident.ident.clone(),
        _ => {
            return syn::Error::new_spanned(
                &closure.inputs,
                "`ensures` takes a closure with one plain name, such as `|result| ...`",
            )
            .to_compile_error()
            .into()
        }
    };
    let condition = *closure.body;
    let text = condition.to_token_stream().to_string();
    let return_type: Type = match &function.sig.output {
        ReturnType::Default => parse_quote!(()),
        ReturnType::Type(_, ty) => (**ty).clone(),
    };
    let body: Block = function.block.as_ref().clone();

    let wrapped: Block = parse_quote! {{
        let __tpt_result = (|| -> #return_type #body)();
        {
            let #binder = &__tpt_result;
            debug_assert!(#condition, "postcondition failed: {}", #text);
        }
        __tpt_result
    }};
    function.block = Box::new(wrapped);
    function.into_token_stream().into()
}

fn entry_check(condition: Expr, mut function: ItemFn, label: &str) -> TokenStream {
    let text = condition.to_token_stream().to_string();
    let check: syn::Stmt = parse_quote! {
        debug_assert!(#condition, "{}: {}", #label, #text);
    };
    function.block.stmts.insert(0, check);
    quote!(#function).into()
}
