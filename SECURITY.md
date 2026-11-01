# Security and Soundness Policy

tpt-proof is a verification tool. A soundness bug, meaning the tool accepting a proof of something false, is treated as a security issue.

## Reporting

Do not open a public issue for a soundness bug or a kernel vulnerability.

Report it privately to: **[TODO: security contact email]**

Include a minimal reproducing proof term or Rust snippet, the version, and the expected result.

## Scope

- Kernel acceptance of an invalid proof: **critical**.
- Translation or VC generation that omits a check: **high**.
- Crashes or resource exhaustion in the tooling: **normal**.

## Response

We aim to acknowledge reports within 7 days and to publish a fix and advisory once a patched release is available.
