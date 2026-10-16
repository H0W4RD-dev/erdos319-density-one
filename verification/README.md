# Author self-check: passed at the selected proof commit

The submitted Lean proof establishes the full **leading asymptotic** in
Erdős #319 under the fixed-sign definition on printed page 43 of
Erdős--Graham (1980). This is a self-check of a candidate solution, not
independent human mathematical review or a prize decision.

**Selected proof commit:** `ed555ed4120225800a6c642e6ba81704d5ed6b11`.
The later commit containing this report adds evidence without changing
any of the seven proof/build inputs in `results.json`.

- **Original-problem correspondence:** yes, for its leading asymptotic.
  The literal bridge covers all interval denominators, fixed signs ±1,
  inherited signs on proper subsums, and the maximum over every qualifying
  subset. The eventual witness is explicitly nonempty.
- **Actual checks at this commit:** passed. Both submitted modules built
  from source with warnings as errors; all 149 expected transitive axiom
  outputs were obtained; both module replays returned exit code zero.
- **Complete result at the checked scope:** yes. The endpoints have no
  extra mathematical hypotheses or assumed existence inputs. They do not
  give exact finite maxima or a sharp lower-order deficit.
- **Lean completeness:** meets the mechanical and statement-comparison
  requirements at this checked scope. Maintainer acceptance, authorship,
  priority, recipient identity and award eligibility remain unestablished.

## Scope and statement correspondence

Original source: [Erdős--Graham (1980), printed page 43, PDF page 39](https://www.math.ucsd.edu/~fan/ron/papers/80_11_number_theory.pdf#page=39).
The relevant original page was visually inspected. It asks how large a set
in `{1,...,N}` can be with a signed zero reciprocal sum and no proper
nonempty zero subsum under those same signs.

| Original requirement | Formal evidence | Correspondence |
| --- | --- | --- |
| Distinct positive denominators at most N | `Finset ℕ`, `Finset.Icc 1 N` | Both endpoints are included; no repeated denominators. |
| One fixed sign ±1 for each denominator | `LiteralPrimitive`, `literalPrimitive_iff` | The literal interface uses integer signs; the internal interface uses units of ℤ. Their equivalence is proved. |
| Zero total reciprocal sum | `LiteralPrimitive`, final witness theorem | Exact rational equality, not a numerical approximation. |
| No proper nonempty zero subsum with inherited signs | Same δ in the total and every subset; literal equivalence | The definition does not permit choosing new signs when testing a subset. |
| Largest size among all qualifying subsets | `literal_maximum` and `maxSize_isGreatest` | The maximum is attained over the full interval powerset. |
| Leading asymptotic | `erdos_problem_319_limit`, `original_problem_density_one` | The exact maximum divided by N tends to 1. |
| Nonempty near-full witnesses for all sufficiently large N | `original_problem_nonempty_witnesses` | For every 0 < ε < 1, there are nonempty literal witnesses of size at least (1−ε)N. |

`Erdos319Formal.erdos_problem_319_witnesses` additionally writes out the
integer sign function, the total sum and every proper subsum explicitly,
for every positive ε. The final problem theorems are closed declarations;
the earlier reductions with explicit analytic hypotheses are intermediate
lemmas, not the final result.

## Execution and trust scope

See [results.json](results.json) and the raw logs alongside this report.
Lean is `4.35.0-rc2`; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. All dependency checkouts matched
their manifest revisions and had clean tracked files. Matching imported
dependency caches were reused; the two submitted library modules were
rebuilt from their source. This was a local Windows author self-check,
not a claim of a credential-isolated execution environment.

| Check | Result | Evidence |
| --- | --- | --- |
| Both submitted library modules | Exit 0; clean source build | [proof-build.log](proof-build.log) |
| Final statements, definitions and 149 axiom closures | Exit 0; all expected outputs present | [axiom-audit.log](axiom-audit.log) |
| Kernel replay of `Erdos319` | Exit 0 | [kernel-replay-Erdos319.log](kernel-replay-Erdos319.log) |
| Kernel replay of `Submission` | Exit 0 | [kernel-replay-Submission.log](kernel-replay-Submission.log) |
| Committed bytes of seven frozen proof/build inputs | Equal to the checked input bytes | [source-binding.json](source-binding.json) |
| Pinned dependency revisions and tracked-file cleanliness | All matched and clean | [dependency-working-trees.json](dependency-working-trees.json) |

All listed axiom closures are subsets of
`{propext, Classical.choice, Quot.sound}`. Each of the three final
problem theorems uses exactly those standard axioms. There is no observed
`sorryAx`, custom mathematical axiom or native-computation axiom in the
audited endpoint closures. The submitted source has no additional
kernel-skipping or environment-modifying proof mechanism in its trust scan.

Verification levels completed: static statement review, actual Lean
compilation and target/axiom checks, and kernel replay of the submitted
modules. The replay uses imported environments; it is not a replay of all
Mathlib and Lean dependencies from scratch. An external independently
defined checker and independent human review are not claimed.

## Attribution, prior work and award limits

The [authorship record](../AUTHORSHIP.md) identifies the requested team,
substantial AI assistance, adopted background proofs and the limits of
individual contribution evidence. The [prior-work disclosure](../PRIOR_WORK.md)
records the earlier density-one manuscript and complete-formalization
claim in awards PR #4669. This self-check does not verify or invalidate
those earlier submissions and does not establish a priority replacement.

The author self-check supports mathematical and formal review; it does not
approve a catalog merge, open a public-review clock, verify any person's
identity or establish an entitlement to payment.
