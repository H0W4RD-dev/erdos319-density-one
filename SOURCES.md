# Mathematical and formal sources

- **Original problem:** P. Erdős and R. L. Graham, *Old and New Problems
  and Results in Combinatorial Number Theory* (1980), printed page 43,
  PDF page 39 of the
  [original scan](https://www.math.ucsd.edu/~fan/ron/papers/80_11_number_theory.pdf).
  The choice of signs is fixed when testing every proper subsum.
- **Problem index:** [Erdős #319](https://www.erdosproblems.com/319), and
  [JSP-000265](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000265).
  The original asks for the largest size. Our conclusion supplies its
  leading asymptotic, rather than exact values for every finite input.
- **Dense expansion:** Y. P. Liu and M. Sawhney, *On further questions
  regarding unit fractions*, [arXiv:2404.07113v1](https://arxiv.org/html/2404.07113v1),
  Proposition 5.2 and Lemmas 2.2--2.3. The manuscript records the precise
  hypotheses used. The Lean endpoints do not assume this theorem.
- **Earlier density-one claims and protected-prime method:** see
  [PRIOR_WORK.md](PRIOR_WORK.md), including g-01234 and peilinliu66-dev.
- **Formal analytic background:**
  [`plby/lean-proofs`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/UnitFractions/ForMathlib),
  commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, the `IntegralRPow`,
  `Misc` and `BasicEstimates` files. Existing proofs were ported to
  Lean 4.35.0-rc2 and included between the marked background boundaries
  in `Erdos319.lean`. They include prime and prime-power reciprocal
  estimates, harmonic estimates, and elementary analytic lemmas. The
  remaining upstream unit-fraction modules are not imported. The upstream
  compatibility comments identify their earlier Lean 3 antecedents.
  See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for notices.
- **Mathlib:** `leanprover-community/mathlib4` at
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`, with its separately fetched
  dependencies pinned by `lake-manifest.json`. Mathlib and its dependencies
  retain their own licenses and contributor attribution.

No external proof repository is substituted for the submitted final proof.
The local public-prior-work comparison was performed during submission
preparation; it does not establish a comprehensive priority assessment.
