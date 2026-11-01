// The form the `tpt-proof-macros` attributes expand to for
// `#[requires(x < 100)] #[ensures(|result| *result >= 150)] fn plus100_loose(x: u8) -> u8`.
// The runtime checks are removed by the driver's `tpt_proof_verify` cfg, so only the
// markers and the function's own body reach the translator.
#[doc = "tpt-proof-requires: x < 100"]
#[doc = "tpt-proof-ensures: |result| *result >= 150"]
pub fn plus100_loose(x: u8) -> u8 {
    #[allow(unexpected_cfgs)]
    #[cfg(not(tpt_proof_verify))]
    debug_assert!(x < 100, "{}: {}", "precondition failed", "x < 100");
    #[allow(unexpected_cfgs)]
    #[cfg(not(tpt_proof_verify))]
    {
        let __tpt_result: u8 = (|| -> u8 { x + 100 })();
        {
            let result = &__tpt_result;
            debug_assert!(*result >= 150, "postcondition failed: {}", "*result >= 150");
        }
        return __tpt_result;
    }
    #[allow(unexpected_cfgs)]
    #[cfg(tpt_proof_verify)]
    {
        return { x + 100 };
    }
}
