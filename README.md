# Erdős #319: an alternative density-one proof

This repository gives a candidate proof and Lean formalization of
`maxSize(N) / N → 1` for the fixed-sign minimal reciprocal identities in
Erdős--Graham (1980), printed page 43. It resolves the leading asymptotic;
it does not give the exact maximum for every finite N or a sharp deficit.

**Prior work and prize status:** the protected-prime construction and the
density-one conclusion already appear in
[g-01234's July 16 manuscript](https://github.com/g-01234/erdos-319-density-one/blob/f55a25a29dcb17193918d27506be5e7a5b5d7d40/docs/proof.md).
[Awards PR #4669](https://github.com/TheJustinSunPrize/awards/pull/4669), opened
October 3, claims a complete Lean proof by a different completion route.
We do not claim first discovery, earlier formalization, accepted independent
verification, or an award. See [PRIOR_WORK.md](PRIOR_WORK.md).

Team: Jensen Kohlmeyer (`jenw1n`), Liam Kruer (`lkruer`), Will Howe
(`H0W4RD-dev`), and Grant Huffman (`Ghuffy1`). Research, drafting and Lean
development used substantial OpenAI Codex assistance. See
[AUTHORSHIP.md](AUTHORSHIP.md) for the limits of these credits and
[SOURCES.md](SOURCES.md) for mathematical and formal dependencies.

- [Manuscript PDF](manuscript/erdos319-solution.pdf) and
  [LaTeX source](manuscript/erdos319-solution.tex).
- [Complete proof](Erdos319.lean), importing only Mathlib.
- [Literal statement comparison](Submission.lean), with integer signs ±1,
  a maximum over all subsets of `{1,...,N}`, and nonempty witnesses.
- [Axiom checks](Audit.lean) for the endpoints, bridges and analytic inputs.

The final declarations in `Erdos319.lean` are:

```text
Erdos319Formal.erdos_problem_319
Erdos319Formal.erdos_problem_319_limit
Erdos319Formal.erdos_problem_319_witnesses
```

The three declarations have no additional mathematical hypotheses.
Earlier conditional reductions inside the file are not the final result.

## Reproduce

Install Git, Python 3.10+ and elan/Lake, clone the selected full commit,
and run from this directory:

```sh
python reproduce.py --setup --clean
```

The project pins Lean `4.35.0-rc2`, Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, and all transitive dependencies
in `lake-manifest.json`. `--setup` fetches the matching official Mathlib
cache; it does not update the pins. Omit `--setup` when dependencies are
already available. The runner builds both submitted library modules from
source, checks `Audit.lean`, and replays both modules with `leanchecker`.
It saves exact commands, exit codes, source hashes and raw logs under
`verification/latest/`. These local outputs are ignored by Git.

Equivalent core commands, after setup, are:

```sh
lake build Erdos319 Submission
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker --verbose Erdos319
lake env leanchecker --verbose Submission
```

The expected transitive axiom dependencies for every listed target are
subsets of `{propext, Classical.choice, Quot.sound}`. The source includes
ported analytic background, with existing attribution retained. There is
no assumed Liu--Sawhney theorem standing in for the formal analytic proof.
Kernel replay checks the submitted modules against the pinned imported
environment; it does not independently replay every Mathlib dependency.
There is no claim of independent human mathematical review.

Prize catalog identifier: **JSP-000265**, distinct from Erdős number 319.
Submission and any later personal claim follow the prize's review and
identity rules. Team authorship is not an application for another person's
award. No public-review clock or recipient eligibility is asserted here.
