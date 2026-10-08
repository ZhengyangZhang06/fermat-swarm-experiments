# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1.unit_power_quotient_exponents-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix F, W, s, u, r and k satisfying the hypotheses. Since zero belongs to W, the assumption s⁻¹ ∉ W implies s ≠ 0. Thus every natural power of s is nonzero.
2. Let α be the image in F of the value of u, and let β be the image of the value of u⁻¹. Both α and β belong to W, and the unit identities give αβ = 1. Put f = α s^r/s^k; by hypothesis f belongs to W.
3. Suppose for contradiction that r < k. Set n = k−r−1 in the natural numbers. Since k ≥ r+1, this gives k = r+n+1. The assumptions s ∈ W and β ∈ W imply s^n ∈ W and hence fβs^n ∈ W by closure under multiplication.
4. Compute in F. Commutativity, αβ = 1 and the power laws give fβs^n = ((αβ)s^(r+n))/s^k = s^(r+n)/s^(r+n+1). Since s ≠ 0, cancel the nonzero factor s^(r+n) from the last fraction to obtain fβs^n = s⁻¹. Step 3 therefore puts s⁻¹ in W, contradicting the hypothesis.
5. Thus r < k is impossible. The linear order on the natural numbers yields k ≤ r, as required.

## Key steps

1. Deduce s ≠ 0 from inverse exclusion.
2. Use the unit and its inverse to obtain αβ = 1 inside F.
3. Under r < k, choose n with k = r+n+1 and form fβs^n in W.
4. Cancel nonzero parameter powers to identify this product with s⁻¹.
5. Contradict inverse exclusion and conclude k ≤ r.

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
