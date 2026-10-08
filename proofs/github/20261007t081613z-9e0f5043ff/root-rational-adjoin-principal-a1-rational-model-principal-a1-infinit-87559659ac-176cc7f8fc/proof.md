# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.reciprocal_polynomial_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K,F,s,v with the stated hypotheses. Transcendence implies that every nonzero polynomial has nonzero evaluation at s. In particular s ≠ 0, because the nonzero polynomial X evaluates to s.
2. Fix a nonzero polynomial a and put d = a.natDegree. Define A(T) = Σ_{i=0}^d C(a_i)T^(d−i). Its constant coefficient equals the leading coefficient a_d of a, which is nonzero. A polynomial divisible by T has zero constant coefficient, so T does not divide A. In particular A ≠ 0, and therefore A(s) ≠ 0 by transcendence.
3. Expanding both evaluations and using s ≠ 0 gives s^d a(s⁻¹) = Σ_{i=0}^d a_i s^(d−i) = A(s). Multiplying by s^(−(d : ℤ)) yields a(s⁻¹) = s^(−(d : ℤ)) A(s). Both factors on the right are nonzero.
4. Since T does not divide A, the assumed vanishing property gives v.ord(A(s)) = 0. Applying Place.ord_mul to the nonzero factors and then Place.ord_zpow gives v.ord(a(s⁻¹)) = (−(d : ℤ)) · v.ord(s) + v.ord(A(s)).
5. Substitute v.ord(s) = 1 and v.ord(A(s)) = 0. The result is v.ord(a(s⁻¹)) = −(d : ℤ), which is the required formula for every nonzero a.

## Key steps

1. Deduce that the transcendental parameter is nonzero.
2. Reverse the polynomial and show that its nonzero constant coefficient excludes divisibility by X.
3. Express evaluation at the inverse parameter as a negative power times the reversed-polynomial evaluation.
4. Apply the assumed zero-order property to the reversed polynomial.
5. Use multiplicativity and the integer-power order formula to obtain minus the degree.

## Reference use

### local-project

Queries:
- `finite_place_model|reverse_eval|eval₂_reverse|eval_reverse|transcendental_inv|transcendental_iff_inv`
- `mem_or_inv_mem|isUnit_iff|eq_of_le_of_ne_top|algebraMap_mem|X_dvd_iff|exists.*pow.*dvd|X_pow|trailingDegree|factor.*X`
- `isMaximal.*X|X.*isMaximal|ker.*eval|span_X|eval.*ker`
- `p06_9e0f5043ff_inf_reciprocal_presentation|p06_9e0f5043ff_inf_reciprocal_polynomial_order|p06_9e0f5043ff_inf_valuation_fraction_characterization`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/Reverse.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/Div.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Polynomial/Ideal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Polynomial/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/name-collision-check.json`

The snapshot supplies Place.ext, Place.ord_mul, Place.ord_zpow, polynomial reversal identities, X-divisibility and root-multiplicity factorization, valuation-subring locality, and the quotient-by-X identification with K. No finite_place_model declaration was found in the snapshot; it is an existing ancestor-level DAG dependency, not an accepted library theorem. Proposed identifiers have no searched-source or active-DAG collisions. Project revision 956e8c600d8b95b46948ae5e37b13930b5f3d06b, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and all nine dependencies match their manifests with clean tracked files. All three proposed types elaborate warning-free under the existing isolated import-only Submission interface. Definitional checks verify the canonical FractionRing algebra, polynomial evaluation, and Place subring and residue algebras. Audited supporting declarations use only propext, Classical.choice, and Quot.sound. However, checking the unchanged actual Submission.lean fails on the pre-existing unknown attribute targets AlgebraicCurve.IsCurveOver.instNontrivialKaehler, AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply, and AlgebraicCurve.SemilinearAut.coe_torsion_smul. Consequently actual import Submission validation remains blocked; interface typechecking is not comparator acceptance or authorization to activate children.
