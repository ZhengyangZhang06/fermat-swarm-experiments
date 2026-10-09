<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1.unit_power_quotient_exponents-a1 -->

## Theorem `Submission.p06_9e0f5043ff_vfc_unit_power_quotient_exponents`

Let F be a field, W a subring of F, and s ∈ F satisfy s ∈ W and s⁻¹ ∉ W. Let u be a unit of W, with image ū in F, and let r,k be natural numbers. If ū s^r/s^k belongs to W, then k ≤ r.

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1.unit_power_quotient_exponents-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/244

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_vfc_unit_power_quotient_exponents`

```lean
∀ (F : Type*) [Field F] (W : Subring F) (s : F), s ∈ W → s⁻¹ ∉ W → ∀ (u : Units W) (r k : ℕ), ((u : W) : F) * s ^ r / s ^ k ∈ W → k ≤ r
```

### Frozen project context

`Fermat/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean` at `956e8c600d8b95b46948ae5e37b13930b5f3d06b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

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


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/497

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
