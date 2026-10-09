# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1.polynomial_unit_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, F, their algebra structure, s and w satisfying the hypotheses, and put W = w.toValuationSubring. Since zero belongs to W and the inverse of zero is zero, the exclusion s⁻¹ ∉ W implies s ≠ 0. The valuation-subring property gives s ∈ W or s⁻¹ ∈ W, so s ∈ W. The resulting element of W is not a unit: the image in F of an inverse in W would equal s⁻¹, contradicting its exclusion.
2. The defining property of a project place puts algebraMap K F c in W for every c ∈ K. Together with s ∈ W and closure under finite sums and products, this puts p(s) in W for every polynomial p. Consequently evaluation defines a unital ring homomorphism E : K[T] → W, whose composition with the inclusion W → F is Polynomial.aeval s. Its homomorphism laws follow from the evaluation laws and injectivity of the inclusion.
3. A valuation subring is a local ring. Let m be its maximal ideal, which consists exactly of its nonunits, and let J = E⁻¹(m). This is a proper ideal of K[T]: E(1) = 1 is a unit and hence does not belong to m. By step 1, E(T) is a nonunit, so T ∈ J and the principal ideal (T) is contained in J.
4. The ideal (T) is maximal. Indeed, every polynomial p has the form C(c) + Tq, where c is its constant coefficient, and T divides p exactly when c = 0. In particular, (T) is proper because the constant coefficient of 1 is nonzero. If an ideal I properly contains (T), choose p ∈ I with T not dividing p. Its constant coefficient c is nonzero. Subtracting Tq from p shows C(c) ∈ I, and multiplying by C(c⁻¹) shows 1 ∈ I. Thus I is the whole polynomial ring, proving maximality. Since J is proper and contains (T), it follows that J = (T).
5. Fix any polynomial p. The local-ring unit criterion and the definition of J give: E(p) is a unit if and only if E(p) ∉ m, if and only if p ∉ J. By J = (T), this is equivalent to T not dividing p.
6. If E(p) is a unit, choose a unit u of W with value E(p). Its image in F is p(s), giving the required existential statement. Conversely, if a unit u of W has image p(s), its value and E(p) have the same image in F. Injectivity of W → F identifies them, so E(p) is a unit. Combining this equivalence with step 5 proves the stated biconditional for every p.

## Key steps

1. Use inverse exclusion to place s in W and show that it is a nonunit.
2. Factor polynomial evaluation through a unital ring homomorphism E into W.
3. Contract the maximal ideal to a proper polynomial ideal J containing T.
4. Use constant coefficients to prove maximality of (T), hence J = (T).
5. Translate avoidance of J into being a unit and then into the stated unit witness.

## Reference use

### local-project

Queries:
- `structure Place|def center|center_ne_bot|toValuationSubring_eq_of_forall_mem|mem_or_inv_mem|algebraMap_mem`
- `exists.*X_pow|X_pow.*exists|X_pow_mul.*[a-z]|not_dvd.*iff|exists_eq_pow_mul_and_not_dvd|exists_pow_mul`
- `isUnit_iff|mem_or_inv_mem|IsLocalRing|isUnit.*mem|mem.*isUnit`
- `theorem X_dvd_iff|theorem irreducible_X|lemma irreducible_X|quotientSpanXSubCAlgEquiv`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/Div.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/RingDivision.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`
- `/tmp/p06_vfc_decomposition_p_0ah0j7/CheckTypes.lean`
- `/tmp/p06_vfc_decomposition_p_0ah0j7/CheckTypes.log`
- `/tmp/p06_vfc_decomposition_p_0ah0j7/source-compatibility.json`
- `/tmp/p06_vfc_decomposition_p_0ah0j7/frozen_header_repair.json`

The manifest pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Place.algebraMap_mem' supplies containment of constants; valuation subrings supply mem_or_inv_mem and IsLocalRing; IsLocalRing.notMem_maximalIdeal identifies units. Polynomial.X_dvd_iff and exists_eq_pow_rootMultiplicity_mul_and_not_dvd supply divisibility and the required factorization at zero, so polynomial factorization needs no new node. Consulted sources matched installed sources, and installed mathlib was clean at its pinned revision. The checked library declarations have only propext, Classical.choice and Quot.sound as transitive axioms. Both proposed types elaborated after import Submission in a disposable compiler copy of the node's frozen proof base; subring ring instances and unit multiplication coercions were checked. Both proposed names were absent from run metadata and the imported base. Compiler-copy evidence records the prescribed policy digest, exact omitted lines 9–11, reversible original/build hashes, and a successful Lean absence probe for all 95 targets. Original repository files remain unchanged. These are interface diagnostics, not comparator acceptance of either proposed theorem.
