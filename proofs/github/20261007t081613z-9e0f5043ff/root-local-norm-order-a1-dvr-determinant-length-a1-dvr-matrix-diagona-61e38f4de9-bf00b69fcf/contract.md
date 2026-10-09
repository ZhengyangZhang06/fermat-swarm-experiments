<!-- theorem-id: fermat-p06/root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1.clear_first_column-a1 -->

## Theorem `Submission.p06_9e0f5043ff_sdp_clear_first_column`

Let R be a commutative ring, m a natural number, and B a matrix indexed by Fin (m + 1) in both directions over R. Suppose B(0,0) divides B(i.succ,0) for every i : Fin m. There exists a matrix U of the same size, invertible under matrix multiplication, such that (UB)(0,j) = B(0,j) for every j : Fin (m + 1) and (UB)(i.succ,0) = 0 for every i : Fin m.

Node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1.clear_first_column-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/133

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_sdp_clear_first_column`

```lean
∀ (R : Type*) [CommRing R] (m : ℕ) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R), (∀ i : Fin m, B 0 0 ∣ B i.succ 0) → ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) R, IsUnit U ∧ (∀ j : Fin (m + 1), (U * B) 0 j = B 0 j) ∧ (∀ i : Fin m, (U * B) i.succ 0 = 0)
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

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1.clear_first_column-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put p = B(0,0). For each i : Fin m, divisibility supplies a coefficient a(i) with B(i.succ,0) = p a(i). Since R is commutative, B(i.succ,0) = a(i)p as well. Choose these coefficients simultaneously.
2. Define a square matrix N using Matrix.of: its zeroth row is zero, and N(i.succ,j) equals a(i) if j = 0 and zero otherwise. Thus every column of N except column zero is zero, and N(0,j) = 0 for every j.
3. For arbitrary row s and column t, expand (N N)(s,t) as the sum over k of N(s,k)N(k,t). When k = 0 the second factor is zero; when k ≠ 0 the first factor is zero. Every summand vanishes, so N N = 0.
4. Set U = I - N and W = I + N, with I the matrix identity. Distributing matrix multiplication gives U W = I + N - N - N N = I and W U = I - N + N - N N = I. Consequently U, with inverse W, defines a unit of the matrix ring, so IsUnit U holds for matrix multiplication.
5. The multiplication formula gives (N B)(0,j) = 0 and (N B)(i.succ,j) = a(i)B(0,j), because only the summand with intermediate index zero can remain. Therefore (U B)(0,j) = B(0,j) and (U B)(i.succ,j) = B(i.succ,j) - a(i)B(0,j). Taking j = 0 yields (U B)(i.succ,0) = a(i)p - a(i)p = 0.
6. These identities and the unit from step 4 give every required conclusion. If m = 0, the coefficient family is empty, N is zero and U is the identity, so the same construction and all the assertions remain valid.

## Key steps

1. Choose coefficients expressing the lower entries of column zero as multiples of B(0,0).
2. Put these coefficients in column zero of a matrix N whose zeroth row vanishes.
3. Show N squared is zero by inspecting each multiplication summand.
4. Exhibit I + N as a two-sided inverse to U = I - N.
5. Compute UB to prove preservation of the first row and vanishing below the pivot.

## Reference use

### local-project

Queries:
- `rg -n 'pivot|transvection|hasPrincipalDivisors_of_transcendental' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project --glob '*.lean'`
- `rg -n 'divisible.*pivot|pivot.*divisible|clear_first_column|clear_first_row' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib --glob '*.lean'`
- `sed -n '1,140p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean`
- `sed -n '310,350p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean`
- `sed -n '1180,1236p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `rg -n 'p06_9e0f5043ff_sdp_clear_first_(column|row)' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/p06-sdp-decomposition-219xgs5a/CheckTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Fermat/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Permutation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/README.txt`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/Submission.build.log`
- `/tmp/p06-sdp-decomposition-219xgs5a/CheckTypes.lean`
- `/tmp/p06-sdp-decomposition-219xgs5a/CheckTypes.log`

The manifest pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; the installed mathlib matches and has clean Git status. Transvection.lean supplies single-entry row/column operations, but its packaged pivot reduction uses a field and division. The targeted search for divisible-pivot and first-row/column clearing lemmas returned no matches. Mul.lean and Permutation.lean supply permutation multiplication infrastructure. Neither proposed identifier occurs in the inspected DAG or Submission. Both proposed types passed Lean 4.33.1 elaboration after import Submission in the run's existing import-only interface environment; expanded instance output confirms Matrix.semiring supplies the unit monoid, including for Matrix.of. This is an interface check: the complete frozen Submission has pre-existing unresolved attribute targets, so full-module validation remains outstanding. Axiom checks of Matrix.mul_apply, Matrix.one_submatrix_mul and Matrix.mul_submatrix_one reported only propext, Classical.choice and Quot.sound. No candidate theorem or comparator acceptance is claimed.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/240

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
