//! Compile-fail tests: each file in `tests/ui` must be rejected by the compiler.
//! Set `TRYBUILD=overwrite` to regenerate the expected `.stderr` files.

#[test]
fn invalid_programs_do_not_compile() {
    let cases = trybuild::TestCases::new();
    cases.compile_fail("tests/ui/*.rs");
}
