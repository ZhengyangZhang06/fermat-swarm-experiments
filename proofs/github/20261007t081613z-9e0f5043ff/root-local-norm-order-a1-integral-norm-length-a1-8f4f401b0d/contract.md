<!-- theorem-id: fermat-p06/root.local_norm_order-a1.integral_norm_length-a1 -->

## Theorem `Submission.p06_9e0f5043ff_lno_integral_norm_length`

Let K, E, and L be fields with compatible algebra structures K → E → L, and suppose L/E is finite-dimensional and separable. Let v be a project place of E over K, A = O_v, and B = Place.integralClosureAt L v, with its canonical maps. For every nonzero b ∈ B, there exists n ∈ ℕ such that length_A(B/bB) = n in ℕ∞ and v.ord(Norm_{L/E}(b)) = n in ℤ, where b is mapped into L before taking its norm. No principal-divisor hypothesis is assumed.

Node: `root.local_norm_order-a1.integral_norm_length-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/36

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/57

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_lno_integral_norm_length`

```lean
∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FiniteDimensional E L] [Algebra.IsSeparable E L] (v : AlgebraicCurve.Place K E) (b : AlgebraicCurve.Place.integralClosureAt L v), b ≠ 0 → ∃ n : ℕ, Module.length v.toValuationSubring (AlgebraicCurve.Place.integralClosureAt L v ⧸ Ideal.span ({b} : Set (AlgebraicCurve.Place.integralClosureAt L v))) = (n : ℕ∞) ∧ v.ord (Algebra.norm E (algebraMap (AlgebraicCurve.Place.integralClosureAt L v) L b)) = (n : ℤ)
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

- Parent DAG node: `root.local_norm_order-a1`
- Child DAG node: `root.local_norm_order-a1.integral_norm_length-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the tower, v, and nonzero b. Put A = O_v and B = integralClosureAt L v. The ring A is a DVR with fraction field E, hence is Noetherian, integrally closed, and a principal ideal domain. Its canonical map into L is the composite A → E → L and is injective. Consequently L is torsion-free over A. The hypotheses of IsIntegralClosure.finite and IsIntegralClosure.module_free in the pinned Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean hold, so B is a finite free A-module. The canonical map B → L is injective, and the canonical scalar actions form the required towers.

2. Choose a finite A-basis (e_i) of B. Its images in L are E-linearly independent. Indeed, an E-linear relation has finitely many coefficients. Since E is the fraction field of A, choose a common nonzero denominator d ∈ A making all coefficients integral over the coefficient ring in the elementary sense d c_i ∈ A. Multiplying the relation by d gives an A-linear relation between the e_i, using injectivity of B → L. A-linear independence gives d c_i = 0 for every i, and d ≠ 0 in the field E then gives c_i = 0.

3. The same images span L over E. For any z ∈ L, finite-dimensionality supplies a monic equation z^m + ∑_{i<m} c_i z^i = 0 with c_i ∈ E and m ≥ 1. Choose nonzero d ∈ A with d c_i ∈ A for every coefficient. Multiplying the equation by d^m shows that dz satisfies a monic equation over A: the coefficient of (dz)^i is c_i d^(m−i), which belongs to A because it equals (d c_i)d^(m−i−1). Thus dz is integral over A and belongs to B. Expand dz in the A-basis and divide the resulting equality in L by the nonzero image of d. This expresses z as an E-linear combination of the images of the e_i. Steps 2 and 3 therefore give an E-basis of L.

4. Let T : B → B be multiplication by b, regarded as an A-linear endomorphism. Write D for its matrix in the A-basis and δ = det_A(T). Applying A → E to the coefficients of the identities b e_j = ∑_i D_ij e_i shows that the matrix of multiplication by the image of b on the E-vector space L is the entrywise image of D. Determinants commute with this ring map because their defining finite sums and products do. Hence the image of δ in E is the determinant of multiplication by b on L, which equals Algebra.norm E b by Algebra.norm_apply.

5. The image of b in L is nonzero by injectivity. Multiplication by it on L is invertible, with inverse multiplication by its reciprocal. Multiplicativity of determinants shows that its determinant has a multiplicative inverse, and so is nonzero. By step 4 the image of δ is nonzero; therefore δ itself is nonzero.

6. Apply the sibling theorem p06_9e0f5043ff_lno_dvr_determinant_length to the finite free A-module B and T. Step 5 checks its determinant hypothesis. It gives a natural number n with length_A(B/range(T)) = n and v.ord of the image of δ equal to n.

7. The range of multiplication by b is exactly the principal ideal bB: its elements are precisely b y with y ∈ B, and commutativity identifies this set with Ideal.span {b}. The corresponding quotient identification is A-linear for the canonical quotient scalar action. Consequently the first equality from step 6 is length_A(B/bB) = n. Replacing the image of δ by the field norm using step 4 gives the second required equality. Both use the same n, as claimed.

## Key steps

1. Obtain a finite free A-module structure on the integral closure.
2. Extend an A-basis of the integral closure to an E-basis of L by clearing denominators.
3. Compare the two multiplication matrices and their determinants.
4. Use invertibility of multiplication in L to prove the integral determinant is nonzero.
5. Apply the DVR determinant-length theorem and identify the range with bB.

## Reference use

### local-project

Queries:
- `/runtime/bin/rg -n 'fiberEquiv|inertiaDeg|integralClosureAt|ord_norm|norm_ord' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/runtime/bin/rg -n 'norm.*length|length.*norm|det.*length|length.*det' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory`
- `/runtime/bin/rg -n 'length|span|pow|finrank' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `sed -n '120,230p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `sed -n '115,185p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Norm/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/name-collision-check.json`

The pinned project already supplies integralClosureAt, finite fibers, fiberEquiv, normalized uniformizer orders, and the canonical restriction residue algebra defining inertiaDeg. Mathlib supplies finite free normalization, localization DVRs, length additivity, and scalar-restriction length formulas. No determinant-length or norm-length theorem matched the RingTheory search. Project HEAD and all nine clean dependencies match their recorded revisions; inspected library files and the three project interface files match the snapshot byte-for-byte. The proposed names have no recorded DAG collision. All three proposed types and the residue-algebra, tower-map, and quotient scalar-action checks pass under the inherited isolated import-only Submission shim. Audited imported lemmas use only propext, Classical.choice, and Quot.sound. However, the unchanged authoritative Submission still fails on three pre-existing unavailable attribute targets. Actual Submission import validation remains an activation gate; neither comparator acceptance nor successful authoritative import is claimed.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/724

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
