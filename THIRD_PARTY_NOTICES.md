# Third-party notices

The analytic-background block in `Erdos319.lean` adapts the existing
`IntegralRPow`, `Misc` and `BasicEstimates` sources from
[`plby/lean-proofs`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/UnitFractions/ForMathlib),
commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
Its source-level compatibility comments and source attribution are retained.
The port changes proofs and names where required by Lean 4.35.0-rc2 and
the pinned Mathlib; it is not an unchanged copy of an upstream build.

The accompanying [upstream license notice](licenses/plby-source-LICENSE.txt)
is reproduced verbatim. That notice identifies Apache-2.0 licensing for
external-source files; the complete Apache-2.0 text is in [LICENSE](LICENSE).
This repository does not claim ownership of existing background proofs or
additional rights beyond the licenses of their original contributors.

Mathlib, Lean and separately downloaded dependencies are not vendored and
retain their own licenses. Mathematical source papers and earlier candidate
proofs are cited as sources, not relicensed by this repository.
