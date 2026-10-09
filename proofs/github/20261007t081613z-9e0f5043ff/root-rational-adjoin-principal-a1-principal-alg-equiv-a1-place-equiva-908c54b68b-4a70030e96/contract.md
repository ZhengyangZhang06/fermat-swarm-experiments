<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.principal_alg_equiv-a1.place_equivalence_degree-a1 -->

## Theorem `Submission.p06_9e0f5043ff_pae_place_equivalence_degree`

Let K, E and L be fields with K-algebra structures on E and L, and let e : E ≃ₐ[K] L. There exists an equivalence θ : AlgebraicCurve.Place K E ≃ AlgebraicCurve.Place K L such that, for every place v, (θ v).deg = v.deg and there exists a K-algebra isomorphism r from v.toValuationSubring to (θ v).toValuationSubring satisfying (r a : L) = e (a : E) for every a in v.toValuationSubring. No characteristic, principal-divisor, finite-dimensionality, or finite-residue hypothesis is assumed.

Node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1.place_equivalence_degree-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/44

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_pae_place_equivalence_degree`

```lean
∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] (e : E ≃ₐ[K] L), ∃ θ : AlgebraicCurve.Place K E ≃ AlgebraicCurve.Place K L, (∀ v : AlgebraicCurve.Place K E, (θ v).deg = v.deg) ∧ (∀ v : AlgebraicCurve.Place K E, ∃ r : v.toValuationSubring ≃ₐ[K] (θ v).toValuationSubring, ∀ a : v.toValuationSubring, (r a : L) = e (a : E))
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
- Child DAG node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1.place_equivalence_degree-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, E, L, their field and algebra structures, and e. For a place v of E put A = v.toValuationSubring and define B = {y ∈ L | e⁻¹(y) ∈ A}. Since e⁻¹ is a ring homomorphism, B is a subring. Applying the valuation alternative in A to e⁻¹(y), and using e⁻¹(y⁻¹) = e⁻¹(y)⁻¹, shows that y ∈ B or y⁻¹ ∈ B. Thus B is a valuation subring; equivalently it is A.comap e.symm.toRingHom.
2. For k ∈ K, e⁻¹(algebraMap K L k) = algebraMap K E k belongs to A, so B contains the image of K. If B were the whole field L, then for every x ∈ E the element e(x) would belong to B, giving x ∈ A. This would contradict v.ne_top'. Hence B is proper.
3. Restrict e to a ring isomorphism r₀ : A ≃+* B, with inverse the restriction of e⁻¹. These maps land in the stated subrings by the definition of B, and their compositions are identities because e and e⁻¹ are inverse. To prove that B is a principal ideal ring, let I be any ideal of B. Its inverse image J under r₀ is an ideal of A, hence J = (a) for some a ∈ A. The element r₀(a) belongs to I. Conversely, if b ∈ I, then r₀⁻¹(b) ∈ J, so r₀⁻¹(b) = c a for some c ∈ A. Therefore b = r₀(c)r₀(a). These two inclusions give I = (r₀(a)). Thus every ideal of B is principal.
4. The properties in steps 1–3 define a place Tₑ(v) with valuation subring B. The K-algebra structures on A and B are the restrictions of the ambient K-algebra maps. Consequently r₀(algebraMap K A k) = algebraMap K B k, because their ambient values are related by e.commutes and subtype inclusion is injective. Hence r₀ upgrades to a K-algebra isomorphism rᵥ : A ≃ₐ[K] Tₑ(v).toValuationSubring. By construction, (rᵥ(a) : L) = e(a : E).
5. Apply the construction of steps 1–4 to e⁻¹ to obtain a map Tₑ₋₁ from places of L to places of E. For x ∈ E, membership in the valuation subring of Tₑ₋₁(Tₑ(v)) is equivalent to e(x) ∈ B, which is equivalent to x ∈ A. Thus this subring equals A, and Place.ext gives Tₑ₋₁(Tₑ(v)) = v. For a place w of L with subring C, membership of y ∈ L in the subring of Tₑ(Tₑ₋₁(w)) reduces to e(e⁻¹(y)) ∈ C, hence to y ∈ C. Place.ext similarly gives Tₑ(Tₑ₋₁(w)) = w. These maps therefore define an equivalence θ with forward map Tₑ.
6. Fix v and its isomorphism rᵥ. A ring isomorphism preserves and reflects units: it sends a unit and its inverse to mutually inverse elements, and the inverse isomorphism proves reflection. In each local valuation ring the maximal ideal consists of nonunits. Therefore rᵥ carries the maximal ideal of A exactly onto the maximal ideal of B.
7. Define the induced residue-field map by [a] ↦ [rᵥ(a)]. Step 6 makes it well-defined: differences in the first maximal ideal map into the second. The map induced by rᵥ⁻¹ is its inverse, and ring operations descend from those of rᵥ. Since rᵥ commutes with the restricted K-algebra maps and the residue algebra maps are their composites with the quotient maps, this is a K-algebra isomorphism κ(v) ≃ₐ[K] κ(θ(v)). This is precisely the construction supplied by IsLocalRing.ResidueField.mapAlgEquiv.
8. Its underlying K-linear equivalence preserves Module.finrank by LinearEquiv.finrank_eq. That theorem follows from equality of the lifted cardinal ranks and application of Cardinal.toNat, so it requires no finite-dimensionality assumption. Since Place.deg is the finrank of the residue field over K, it follows that (θ(v)).deg = v.deg. The equivalence θ, these degree equalities, and the isomorphisms rᵥ with the compatibility equation from step 4 establish the entire conclusion.

## Key steps

1. Pull each valuation subring back along e.symm and prove it contains K and remains proper.
2. Restrict e and transfer principality of ideals by pulling back an arbitrary ideal and transporting its generator.
3. Upgrade the restriction to a K-algebra isomorphism and use e.symm and Place.ext to obtain an equivalence of places.
4. Transport maximal ideals via preservation and reflection of units, obtaining residue K-algebra isomorphisms.
5. Apply unrestricted finrank invariance to prove preservation of place degrees.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/737

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
