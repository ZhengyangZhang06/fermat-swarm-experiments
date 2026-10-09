<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.principal_alg_equiv-a1.compatible_order_invariance-a1 -->

## Theorem `Submission.p06_9e0f5043ff_pae_compatible_order_invariance`

Let K, E and L be fields with K-algebra structures on E and L. Let e : E ≃ₐ[K] L, let v : AlgebraicCurve.Place K E and w : AlgebraicCurve.Place K L, and let r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring. Suppose that (r a : L) = e (a : E) for every a in v.toValuationSubring. Then for every nonzero f ∈ E, w.ord (e f) = v.ord f. No characteristic, principal-divisor, finite-dimensionality, or finite-residue hypothesis is assumed.

Node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1.compatible_order_invariance-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/44

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_pae_compatible_order_invariance`

```lean
∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] (e : E ≃ₐ[K] L) (v : AlgebraicCurve.Place K E) (w : AlgebraicCurve.Place K L) (r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring), (∀ a : v.toValuationSubring, (r a : L) = e (a : E)) → ∀ f : E, f ≠ 0 → w.ord (e f) = v.ord f
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

- Parent DAG node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1.compatible_order_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated fields, algebra structures, e, v, w and r, and assume the compatibility equation. Write A = v.toValuationSubring and B = w.toValuationSubring. Fix f ∈ E with f ≠ 0. The project's Place instance makes A a discrete valuation ring: A is a proper principal valuation subring. By IsDiscreteValuationRing.exists_irreducible choose π ∈ A with Irreducible π.
2. Put π' = r(π) ∈ B. Ring isomorphisms preserve and reflect units. Thus π' is not a unit, since otherwise π would be one. If π' = ab in B, applying r⁻¹ gives π = r⁻¹(a)r⁻¹(b). Irreducibility of π implies that r⁻¹(a) or r⁻¹(b) is a unit, and applying r implies that a or b is a unit. Therefore π' is irreducible.
3. Put n = v.ord f. By Place.exists_unit_mul_zpow applied to f ≠ 0 and π, there exists u ∈ Aˣ such that f = (u : E)(π : E)^n. Here the ambient value of u means the composite coercion from Aˣ to A to E, and the power is an integer power in E.
4. Transport u to a unit u' ∈ Bˣ by applying r to its value and inverse. The unit identities follow because r preserves multiplication and one. Its value in B is r(u : A). The compatibility hypothesis consequently gives (u' : L) = e(u : E), and also (π' : L) = e(π : E).
5. Apply e to the factorization in step 3. A field isomorphism preserves multiplication, inverses and hence integer powers. Substituting the two equations from step 4 therefore gives e(f) = (u' : L)(π' : L)^n.
6. Apply Place.ord_unit_smul_zpow at w to the unit u', the irreducible π' from step 2, and the integer n. It gives w.ord((u' : L)(π' : L)^n) = n. Rewriting by step 5 and n = v.ord f proves w.ord(e(f)) = v.ord f, as required for every nonzero f.

## Key steps

1. Choose an irreducible uniformizer in the discrete valuation ring of v.
2. Prove that its image under r remains irreducible.
3. Factor f as a valuation-ring unit times the uniformizer raised to v.ord f.
4. Transport the unit and factorization using compatibility with e and preservation of integer powers.
5. Evaluate the transported normalized order with Place.ord_unit_smul_zpow.

## Reference use

### local-project

Queries:
- `rg -n 'HasPrincipalDivisors|exists_unit_mul_zpow|ord_unit_smul_zpow|mapAlgEquiv' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`
- `grep fallback: def congrEquiv|def congrRingEquiv|congrEquiv_apply|hasPrincipalDivisors.*[Ee]quiv|[Ee]quiv.*[Hh]asPrincipalDivisors`
- `grep fallback: HasPrincipalDivisors|exists_unit_mul_zpow|ord_unit_smul_zpow`
- `grep fallback: mapEquiv|map_residue`
- `grep fallback: (theorem|def) finrank_eq|theorem of_surjective|theorem exists_irreducible|theorem irreducible_iff`
- `#print axioms AlgebraicCurve.Place.ext`
- `#print axioms AlgebraicCurve.Place.exists_unit_mul_zpow`
- `#print axioms AlgebraicCurve.Place.ord_unit_smul_zpow`
- `#print axioms AlgebraicCurve.Divisor.degree_single`
- `#print axioms IsLocalRing.ResidueField.mapAlgEquiv`
- `#print axioms LinearEquiv.finrank_eq`
- `#print axioms IsDiscreteValuationRing.exists_irreducible`
- `#print axioms IsPrincipalIdealRing.of_surjective`
- `#print axioms MulEquiv.irreducible_iff`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/CheckTypes.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/provenance-check.json`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/name-collision-check.json`

rg was unavailable; searches continued with grep. The project supplies Place.ext, the DVR instance, normalized-order decomposition and evaluation, divisor degree, and analogous automorphism transport proofs. No general cross-field principal-divisor transport theorem or definition of Place.congrEquiv was found; the latter name occurs only in attribute lists. Mathlib supplies valuation-subring comap, residue algebra equivalences, uniformizers, and finrank invariance without finite-dimensionality. Snapshot revisions match project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; pinned dependency tracked trees are clean. Inspected supporting declarations use only propext, Classical.choice, and Quot.sound. Both proposed types elaborate in the existing isolated import-only Submission interface, and proposed names have no detected collisions. The authoritative Submission source still fails on pre-existing unknown attribute targets, so its required import gate remains unsatisfied.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/682

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
