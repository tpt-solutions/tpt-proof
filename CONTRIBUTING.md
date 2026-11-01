# Contributing to tpt-proof

Thanks for your interest. tpt-proof is pre-alpha and the design is in [SPEC.md](SPEC.md).

## Before you start

- Read [SPEC.md](SPEC.md) and check [TODO.md](TODO.md) for open work.
- For anything large, open an issue first so the design can be agreed.

## Ground rules

- **The kernel is the trusted base.** Changes to `crates/tpt-proof-kernel` need a second reviewer and an update to [kernel/AUDIT.md](kernel/AUDIT.md). The kernel must keep zero dependencies and stay under 5,000 lines. CI enforces both.
- **Axioms expand the TCB.** Adding an axiom requires a justification in its doc comment and a dedicated PR.
- **Fail loudly.** A verifier must never report "probably correct". Use the explicit result states from SPEC.md §2.
- Code and comments follow the surrounding style. Keep comments short and about why, not what.

## Checks

Run these before opening a PR:

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo deny check
```

## Licensing

tpt-proof is dual-licensed under MIT OR Apache-2.0. Unless you say otherwise, any contribution you submit is licensed under the same terms, as described in the Apache-2.0 license. Do not submit code you do not have the right to contribute.

## Commit messages

Use a short imperative subject. Keep the body to the reasoning. Commits that include AI assistance may carry Co-Authored-By trailers.
