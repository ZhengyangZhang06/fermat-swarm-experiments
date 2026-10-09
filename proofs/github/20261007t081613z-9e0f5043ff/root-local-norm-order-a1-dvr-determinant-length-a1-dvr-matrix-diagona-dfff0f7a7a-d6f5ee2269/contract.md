<!-- theorem-id: fermat-p06/root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1 -->

## Theorem `Submission.p06_9e0f5043ff_dmd_split_divisible_pivot`

Let R be a commutative ring, m ∈ ℕ, D a square matrix indexed by Fin (m + 1) over R, and r,c : Fin (m + 1). Assume that p = D(r,c) divides every entry of D. Then there exist square matrices P,Q indexed by Fin (m + 1), invertible under matrix multiplication, and a square matrix C indexed by Fin m, such that P D Q has entry p at (0,0), zero at every (0,j.succ) and (i.succ,0), and entry C(i,j) at every (i.succ,j.succ). No nonvanishing or determinant hypothesis is required.

Node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/96

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/144, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/145

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_dmd_split_divisible_pivot`

```lean
∀ (R : Type*) [CommRing R] (m : ℕ) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (r c : Fin (m + 1)), (∀ i j, D r c ∣ D i j) → ∃ (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (C : Matrix (Fin m) (Fin m) R), IsUnit P ∧ IsUnit Q ∧ P * D * Q = Matrix.of (fun i j => Fin.cases (Fin.cases (D r c) (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => C i' j') j) i)
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

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data and put p = D(r,c). Let σ swap 0 and r, and let τ swap 0 and c, on Fin (m + 1). Define permutation matrices S and T by S(i,j) = 1 when j = σ(i), and zero otherwise, and T(i,j) = 1 when i = τ(j), and zero otherwise. The matrix multiplication formula and σ² = τ² = identity give S² = T² = I. Thus S and T are invertible, each with itself as inverse. Set B = S D T. Multiplication gives B(i,j) = D(σ(i),τ(j)); hence B(0,0) = p and p divides every entry of B.
2. For each i : Fin m, choose α(i) with B(i.succ,0) = α(i)p. Such a choice follows from divisibility and commutativity. For each j : Fin m, choose β(j) with B(0,j.succ) = pβ(j). These choices also make sense when m = 0, since the indexing types are then empty.
3. Define N by N(i.succ,0) = α(i), with all its other entries zero. Define M by M(0,j.succ) = β(j), with all its other entries zero. Both satisfy N² = 0 and M² = 0. Indeed, in each summand N(i,k)N(k,j), the first factor is zero unless k = 0, and when k = 0 the second factor is zero. In each summand M(i,k)M(k,j), the second factor is zero unless k = 0, and when k = 0 the first factor is zero. Set U = I - N and V = I - M. Distributivity now gives U(I + N) = (I + N)U = I and V(I + M) = (I + M)V = I. These are two-sided matrix inverses.
4. Set H = U B. Its entries satisfy H(0,j) = B(0,j) and H(i.succ,j) = B(i.succ,j) - α(i)B(0,j). Therefore H(0,0) = p and H(i.succ,0) = α(i)p - α(i)p = 0. Define C(i,j) = H(i.succ,j.succ).
5. Set Z = H V. Because column zero of M is zero, Z(i,0) = H(i,0). For each j : Fin m, multiplication gives Z(i,j.succ) = H(i,j.succ) - H(i,0)β(j). Thus Z(0,j.succ) = pβ(j) - pβ(j) = 0, while Z(i.succ,j.succ) = H(i.succ,j.succ) = C(i,j). Also Z(0,0) = p and Z(i.succ,0) = 0. These four entry formulas identify Z with the matrix expressed by the nested Fin.cases in the conclusion.
6. Take P = U S and Q = T V. Their two-sided inverses are S(I + N) and (I + M)T, respectively, by the inverse identities from steps 1 and 3. Hence IsUnit P and IsUnit Q hold for matrix multiplication. Finally, associativity gives P D Q = U(S D T)V = U B V = H V = Z. Together with the entry formulas and the chosen C, this proves the exact conclusion.

## Key steps

1. Move the specified pivot to (0,0) using self-inverse permutation matrices.
2. Choose coefficients expressing the first-column and first-row entries as multiples of the pivot.
3. Construct square-zero matrices N and M, giving explicit inverse pairs I − N, I + N and I − M, I + M.
4. Left multiplication clears the first column below the pivot.
5. Right multiplication clears the first row and preserves the lower-right block.
6. Compose the operations, exhibit two-sided inverses, and verify the four cases of the resulting block matrix.

## Reference use

### local-project

Queries:
- `exists_irreducible|eq_unit_mul_pow_irreducible|exists.*pow.*[Ii]rreducible|eq_unit_mul_pow`
- `transvection_mul|mul_transvection|isUnit_transvection|det_fromBlocks|det_fin_succ|fromBlocks.*mul|mul_fromBlocks`
- `smithNormalForm|smith_normal_form|matrix_diagonalization|dividing_pivot|pivot_block`
- `def of|abbrev of|instance.*[Mm]onoid|instance.*[Rr]ing|instMul|protected def mul`
- `p06_9e0f5043ff_dmd_finite_family_dividing_member|p06_9e0f5043ff_dmd_split_divisible_pivot`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/FreeModule/PID.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/README.txt`
- `/tmp/p06-dmd-decomposition-9e0f5043ff/CheckTypes.interface-check.log`
- `/tmp/p06-dmd-decomposition-9e0f5043ff/AuditReferences.log`

The snapshot pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. DVR Basic supplies exists_irreducible and eq_unit_mul_pow_irreducible; PlacesOverDVR uses both. Matrix sources provide elementary-operation identities, block determinants, and the matrix multiplication instances. FreeModule/PID contains an abstract basis Smith-normal-form theorem. The project search found no matches for smithNormalForm, smith_normal_form, matrix_diagonalization, dividing_pivot, or pivot_block. Installed dependency revisions match their pins and have clean tracked trees; the four directly checked mathlib source files match the snapshot byte-for-byte. Axiom audits of the referenced DVR and matrix lemmas report only propext, Classical.choice, and Quot.sound. Both proposed names are absent from the searched DAG metadata and imported environment. Both exact type expressions pass the available import Submission interface check, and explicit instance output confirms matrix multiplication and the monoid from Matrix.semiring. Limitation: that existing Submission cache is an import-only shim; its README records pre-existing unknown attribute targets blocking the complete frozen Submission build. These checks therefore do not establish exact-source build or comparator acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/516

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
