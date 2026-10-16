# Earlier public work and contribution scope

Checked on October 16, 2026. This is a disclosure, not a priority decision.

1. **g-01234, July 16, 2026.**
   [Pinned manuscript](https://github.com/g-01234/erdos-319-density-one/blob/f55a25a29dcb17193918d27506be5e7a5b5d7d40/docs/proof.md).
   It claims `c(N)/N → 1` under the same fixed-sign primitivity definition.
   Its modular atom uses large-prime blocks, an extra reciprocal connector,
   small reciprocal prime cost, and rigidity of subsums with denominator
   coprime to the protected primes. These are also the structural ideas
   used in our finite CRT construction and final primitivity argument.
   Its completion follows a prime-power descent using modular-inverse
   subset sums and a terminal unit-fraction reservoir. The manuscript
   explicitly describes its accompanying Lean theorem as conditional on
   two published-input interfaces, rather than a full global formal proof.

2. **peilinliu66-dev, October 3, 2026.**
   [Awards PR #4669](https://github.com/TheJustinSunPrize/awards/pull/4669);
   [selected proof revision](https://github.com/peilinliu66-dev/jsp265-erdos319-density-one/tree/72545d3e68e8881e2f89f4744067583aaa61fc9e).
   It credits the first manuscript and claims a complete global Lean proof
   of the density-one asymptotic using a thinned-prime inverse-sum route
   and a fixed terminal reservoir. We inspected its statement, mathematical
   description and submitted evidence, but have not independently rebuilt
   or verified that repository. The PR was open when checked. We neither
   assert its acceptance nor allege a defect in its proof.

3. Other JSP-000265 PRs found in the public search include #4597, #3087,
   #2234, #2598 and #904. Some concern finite examples or older incomplete
   formalizations; they are not a basis for ignoring #4669's full claim.

Our manuscript uses Liu--Sawhney Proposition 5.2 for dense exact expansions
avoiding a fixed set of primes. Our formalization is a single proof file
with Mathlib-only imports, including ported and attributed background
estimates and complete proofs of the needed analytic steps. The final
theorems prove the ratio limit and explicit fixed-sign witnesses.

This is an alternative exposition and formalization, not a claim to the
first density-one theorem, the first protected-prime construction or the
earliest complete Lean proof. A later passing proof cannot by itself
displace an earlier accepted source under the prize's rules. We request
mathematical and formal review with these prior sources disclosed; any
award eligibility and priority remain for the maintainers to decide.
