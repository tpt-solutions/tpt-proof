# Contributing to tpt-proof

Contributions are made through **GitHub issues only**. Open an issue at
https://github.com/tpt-solutions/tpt-proof/issues to:

- report a bug, including a soundness bug (a proof or verification result the tool should not accept);
- propose a feature or a design change;
- ask a question about the design in [spec.txt](spec.txt) or the plan in [TODO.md](TODO.md).

Pull requests are not accepted from outside contributors. Maintainers make all code changes.

## Writing a useful issue

- Say what you ran, what you expected, and what happened.
- For a soundness bug, include a minimal reproducing proof term or Rust snippet, the version, and the result the tool gave.
- For a design change, say why the current design does not work and what you propose instead. Large changes are agreed in the issue before anyone writes code.

## Ground rules

- **The kernel is the trusted base.** Changes to `crates/tpt-proof-kernel` need an update to [kernel/AUDIT.md](kernel/AUDIT.md). The kernel must keep zero dependencies and stay under 5,000 lines. CI enforces both.
- **Axioms expand the TCB.** Adding an axiom requires a justification in its doc comment, a dedicated change, and an entry in `kernel/AUDIT.md`.
- **Fail loudly.** A verifier must never report "probably correct". Use the explicit result states from spec.txt §2.

## Licensing

tpt-proof is dual-licensed under MIT OR Apache-2.0. Unless you say otherwise, any contribution you intentionally submit for inclusion is licensed under the same terms, as described in the Apache-2.0 license. Do not submit material you do not have the right to contribute.
