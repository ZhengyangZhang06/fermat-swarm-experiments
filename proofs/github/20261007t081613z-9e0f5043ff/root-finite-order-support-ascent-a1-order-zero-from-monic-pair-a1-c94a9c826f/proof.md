# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_order_support_ascent-a1`
- Child DAG node: `root.finite_order_support_ascent-a1.order_zero_from_monic_pair-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated fields, compatible algebra structures, integral extension, place w, nonzero element f, and monic polynomials P and Q satisfying the two equations and coefficient hypotheses. The integral-extension hypothesis permits the existing restriction construction v = w.restrict E. By Place.restrict_toValuationSubring, its valuation subring is w.toValuationSubring.comap (algebraMap E L). Thus membership of a coefficient in this restricted subring means that its image under algebraMap E L belongs to w.toValuationSubring; this is Place.mem_restrict_iff.
2. Form P_L = P.map (algebraMap E L) and Q_L = Q.map (algebraMap E L). Both are monic because a unital ring homomorphism preserves the leading coefficient 1 of a monic polynomial. Their coefficients are the images of the corresponding coefficients of P and Q. Hence step 1 and the coefficient hypotheses put every coefficient of P_L and Q_L in w.toValuationSubring.
3. Evaluation of a mapped polynomial equals eval₂ of the original polynomial along the coefficient map. The assumed equations therefore give P_L.eval f = 0 and Q_L.eval (f⁻¹) = 0. Applying Place.mem_of_eval_monic_eq_zero separately to these two monic polynomials yields f ∈ w.toValuationSubring and f⁻¹ ∈ w.toValuationSubring.
4. Let a and b be the elements of w.toValuationSubring represented by f and f⁻¹ with these membership proofs. Since f ≠ 0, their images in L multiply to 1 in either order. Injectivity of the subring inclusion implies ab = 1 and ba = 1 inside the subring. Thus a, with inverse b, defines a unit u of w.toValuationSubring.
5. Place.ord_coe_unit states that the image of u in L has order zero at w. That image is f, so w.ord f = 0, as required.

## Key steps

1. Identify the restricted valuation subring with the comap under algebraMap E L.
2. Map both monic polynomials to L and transfer all coefficient memberships upstairs.
3. Translate the eval₂ equations into root equations for the mapped polynomials.
4. Apply the monic-root lemma to place both f and f⁻¹ in the upstairs valuation ring.
5. Construct the resulting valuation-ring unit and apply ord_coe_unit.

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
