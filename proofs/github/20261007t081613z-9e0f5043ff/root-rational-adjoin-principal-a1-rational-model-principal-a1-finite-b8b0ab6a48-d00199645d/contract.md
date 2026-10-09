<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.residue_degree-a1 -->

## Theorem `Submission.p06_9e0f5043ff_fpm_residue_degree`

Let K and F be fields with a K-algebra structure on F, let x ∈ F be transcendental over K, and let q ∈ K[T] be monic and irreducible. Let v : AlgebraicCurve.Place K F satisfy: for every f ∈ F, f belongs to v.toValuationSubring exactly when f = a(x)/b(x) for polynomials a,b with q not dividing b. Then v.deg = q.natDegree. No assumption that all elements of F are rational expressions in x is required.

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.residue_degree-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/73

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/117, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/118

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_fpm_residue_degree`

```lean
∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F), Transcendental K x → ∀ q : Polynomial K, q.Monic → Irreducible q → ∀ v : AlgebraicCurve.Place K F, (∀ f : F, f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K, ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) → v.deg = q.natDegree
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

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.residue_degree-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put R = K[T], e(a) = a(x), A = v.toValuationSubring, and κ = v.ResidueField, with their canonical K-algebra structures. Evaluation e is injective. Irreducibility gives q ≠ 0 and says q is not a unit, so q does not divide 1. The membership hypothesis with denominator 1 puts every e(a) in A. If q does not divide a, then a and e(a) are nonzero, and the permitted fraction e(1)/e(a) belongs to A. Consequently e(a) is a unit of A.
2. The element e(q) is a nonunit of A. Otherwise its inverse would belong to A and have a representation e(a)/e(b) with q not dividing b. Cross multiplication, using e(q) ≠ 0 and e(b) ≠ 0, would give e(b) = e(q a), and injectivity would imply q divides b, a contradiction. Since A is local, e(q) belongs to its maximal ideal and has zero residue.
3. Compose the K-algebra evaluation map R → A with the canonical residue map A → κ to obtain a K-algebra homomorphism φ. If q divides a, then e(a) is an A-multiple of e(q), so φ(a) = 0. If q does not divide a, step 1 makes e(a) a unit; its image under the residue homomorphism is a unit in the nontrivial field κ and hence is nonzero. Therefore φ(a) = 0 if and only if q divides a. Its kernel is exactly the principal ideal (q).
4. The map φ is surjective. Indeed, given r ∈ κ, choose h ∈ A with residue r, using surjectivity of the residue quotient map. Represent h = e(a)/e(b) with q not dividing b. The greatest common divisor of q and b is a unit, since a nonunit common divisor would be associated to the irreducible q and would force q to divide b. The Euclidean algorithm thus gives u q + t b = 1. Applying φ and using φ(q) = 0 gives φ(t)φ(b) = 1. The identity h e(b) = e(a) in A gives r φ(b) = φ(a). Multiplying by φ(t) yields r = φ(a t), proving surjectivity.
5. Since φ is a surjective K-algebra homomorphism with kernel (q), it induces a K-algebra isomorphism R/(q) → κ. Explicitly, the induced map sends the class of a to φ(a); the kernel calculation makes it well-defined and injective, and step 4 makes it surjective. Thus κ and R/(q) have equal K-dimension.
6. Let d = q.natDegree. This number is positive because q is nonzero and a degree-zero polynomial over K would be a unit. Division by the monic polynomial q writes every a as q s + t, where t is zero or has degree less than d. Therefore the residue classes of 1,T,…,T^(d−1) span R/(q). For independence, a linear relation among these classes gives a polynomial p = Σ_{i<d} cᵢ T^i whose class is zero, so q divides p. If p were nonzero, writing p = q s would give s ≠ 0 and natDegree p = d + natDegree s ≥ d. This contradicts the degree bound for p. Hence p = 0, and comparing coefficients gives every cᵢ = 0. The displayed classes form a basis indexed by Fin d.
7. It follows that Module.finrank K (R/(q)) = d, and step 5 transfers this equality to κ. By the project's definition v.deg = Module.finrank K v.ResidueField, we conclude v.deg = q.natDegree.

## Key steps

1. Embed polynomial evaluations in the valuation subring and identify the evaluations prime to q as units.
2. Show q(x) has zero residue by proving it is a nonunit.
3. Construct the polynomial-to-residue algebra map and identify its kernel as (q).
4. Use Bézout inverses for permitted denominators to prove surjectivity.
5. Identify the residue field with K[T]/(q) as a K-algebra.
6. Prove the degree-bounded monomial classes form a basis.
7. Transfer finrank and unfold the project's definition of place degree.

## Reference use

### local-project

Queries:
- `structure Place|def deg|def ord|ord_coe_unit|ord.*uniformizer|ord.*irreducible|hasPrincipalDivisors_of_transcendental|finite.*[Pp]lace|placeOfIrreducible|ResidueField|heightOneSpectrumOfIrreducible`
- `placeOfIrreducible|heightOneSpectrumOfIrreducible|residue.*[Aa]dj|finrank.*[Aa]djoinRoot|IsLocalization.*AtPrime|exists.*pow.*dvd`
- `finrank|basis|quotient|Quotient`
- `exists.*pow.*dvd|pow.*not_dvd|multiplicity.*finite|FiniteMultiplicity`
- `residue_eq_zero_iff|mem_maximalIdeal|surjective`
- `theorem.*prime|irreducible_iff_prime`
- `p06_9e0f5043ff_fpm_(exists_local_place|normalized_orders|residue_degree)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Multiplicity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/AdjoinRoot.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/PrincipalIdealDomain.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-ff0d532bf4/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-ff0d532bf4/decomposition-typecheck/InspectLibrary.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-ff0d532bf4/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-ff0d532bf4/decomposition-typecheck/Submission.frozen-source-check.log`

The snapshot pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Place requires a proper valuation subring containing K and an IsPrincipalIdealRing proof; its degree is the canonical residue-field finrank. Place.ord_coe_irreducible and Place.ord_coe_unit provide the required normalization. Multiplicity.lean supplies finite prime-power factorization and multiplicity additivity; AdjoinRoot.lean supplies finrank_quotient_span_eq_natDegree; ResidueField/Basic.lean identifies the residue kernel and supplies surjectivity. The targeted P2M search found no matching finite-place construction. Proposed names have no active-DAG or searched-source collisions. All nine installed dependencies match their pinned revisions and have clean tracked files. Audited supporting declarations depend only on propext, Classical.choice and Quot.sound. All proposed types elaborate against the existing isolated import-only Submission interface, whose project definitions match the snapshot byte-for-byte; definitional-equality checks verify the intended subring and residue-field algebra structures. The unchanged actual Submission still fails on three pre-existing unknown attribute targets, so actual import validation remains outstanding. These checks are not comparator acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/312

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
