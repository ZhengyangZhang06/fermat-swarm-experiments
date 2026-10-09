# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_order_support_ascent-a1`
- Child DAG node: `root.finite_order_support_ascent-a1.polynomial_coefficients_integral_off_fa-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, E, their stated field and algebra structures, the finite-support hypothesis H, and a polynomial P. For each i in the finite polynomial support P.support, the coefficient c_i = P.coeff i is nonzero. Consequently S_i = {v : AlgebraicCurve.Place K E | v.ord c_i ≠ 0} is finite by H.
2. Define T = ⋃ i ∈ P.support, S_i. This is a finite union of finite sets, so T is finite.
3. Fix a place v outside T and a natural number i. If P.coeff i = 0, then this coefficient belongs to v.toValuationSubring because every subring contains zero. Otherwise i belongs to P.support. Since v is outside T, it is outside S_i, and therefore v.ord (P.coeff i) = 0.
4. The valuation subring of v is a discrete valuation ring. Choose an irreducible uniformizer π in it, using IsDiscreteValuationRing.exists_irreducible. Apply Place.exists_unit_mul_zpow to the nonzero coefficient. It supplies a unit u of v.toValuationSubring such that P.coeff i = ((u : v.toValuationSubring) : E) * ((π : E) ^ (v.ord (P.coeff i))). The exponent is zero by step 3, so P.coeff i equals the image of u. Thus the coefficient belongs to v.toValuationSubring.
5. The two cases prove coefficient membership for every i at every v outside T. Together with the finiteness of T, this proves the statement.

## Key steps

1. Index the nonzero coefficients by the finite polynomial support.
2. Use the hypothesis to obtain a finite order support for each such coefficient.
3. Take their finite union as the exceptional set.
4. Outside this set, each nonzero coefficient has order zero.
5. Use unit–uniformizer factorization to obtain membership; handle zero coefficients separately.

## Reference use

### local-project

Queries:
- `rg -n 'finite_setOf_restrict_eq|mem_of_eval_monic_eq_zero|exists_unit_mul_zpow|ord_coe_unit|def restrict|HasPrincipalDivisors|hasPrincipalDivisors_of_transcendental' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f --glob '*.lean'`
- `rg -n 'finite.*coeff|coeff.*finite|coeff.*ord|ord.*coeff|mem_of_ord_nonneg|ord_eq_zero_of' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_*.lean`
- `rg -n 'exists_irreducible|theorem isIntegral|isIntegral_of_finite' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`
- `rg -n 'p06_9e0f5043ff_fosa_coefficients_integral_off_finite|p06_9e0f5043ff_fosa_ord_zero_of_monic_pair' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json Submission.lean Definitions Fermat`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1/decomposition-typecheck/Submission.unchanged-check.log`

DivisorClassGroup supplies the DVR instance, unit–uniformizer factorization, and order zero for units. DivisorPushPull defines restriction by valuation-subring comap and supplies mem_restrict_iff; its order-to-membership lemmas are private. PlacesOverDVR supplies mem_of_eval_monic_eq_zero and finite_setOf_restrict_eq, the latter without principal-divisor assumptions. No existing public coefficient-exceptional-set or monic-pair order-zero theorem matched the targeted search. Neither proposed name matched existing DAG reservations or project declarations. Project HEAD matches 956e8c600d8b95b46948ae5e37b13930b5f3d06b; all nine dependencies are clean at their pinned revisions, including mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The three imported project sources match the snapshot and existing interface build byte-for-byte. Both proposed types elaborate under the existing import-only Submission interface. Additional checks verify restriction is definitionally the intended comap and finite-dimensionality supplies Algebra.IsIntegral. The six audited supporting declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. However, the unchanged authoritative Submission still fails on three pre-existing attribute directives naming unavailable declarations. Successful validation through that unchanged module remains blocked; interface checking is not comparator acceptance.
