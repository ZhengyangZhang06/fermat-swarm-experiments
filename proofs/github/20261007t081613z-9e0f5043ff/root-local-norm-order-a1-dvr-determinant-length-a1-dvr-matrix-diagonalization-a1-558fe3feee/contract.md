<!-- theorem-id: fermat-p06/root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1 -->

## Theorem `Submission.p06_9e0f5043ff_dlen_matrix_diagonalization`

Let A be a commutative integral domain that is a discrete valuation ring. For every m ∈ ℕ and square matrix D indexed by Fin m over A with det(D) ≠ 0, there exist square matrices P and Q invertible under matrix multiplication and a function d : Fin m → A such that every d(i) is nonzero and P D Q = diagonal(d). No ordering or divisibility condition on consecutive diagonal entries is asserted.

Node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/57

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/132, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/133

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_dlen_matrix_diagonalization`

```lean
∀ (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (m : ℕ) (D : Matrix (Fin m) (Fin m) A), D.det ≠ 0 → ∃ (P Q : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit P ∧ IsUnit Q ∧ (∀ i, d i ≠ 0) ∧ P * D * Q = Matrix.diagonal d
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

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix A. Choose an irreducible uniformizer π using IsDiscreteValuationRing.exists_irreducible. The pinned factorization theorem says that every nonzero x ∈ A can be written x = uπ^e with u ∈ Aˣ and e ∈ ℕ. If p = uπ^a and x = wπ^b with a ≤ b, then x = p(u⁻¹wπ^(b-a)). Thus p divides x. It also divides zero.

2. We prove the assertion by induction on m. For m = 0, take P and Q to be identity matrices and d to be the unique function on Fin 0. Both matrices are units. All matrices of this empty shape are equal, so the required matrix identity holds, and the nonzero-entry assertion is vacuous.

3. Suppose the assertion holds for m and let D have size m+1 with nonzero determinant. Some entry of D is nonzero: otherwise D is the zero matrix of positive size and has zero determinant. Factor each of its finitely many nonzero entries as in step 1, and choose an entry p whose chosen exponent is minimal. Step 1 implies that p divides every entry. Swap its row with row zero and its column with column zero. Let B be the resulting matrix. These swaps are implemented by invertible permutation matrices, B_(0,0) = p, and p still divides every entry of B.

4. For each i ≠ 0, choose r_i with B_(i,0) = r_i p and replace row i by row i minus r_i times row zero. Each replacement is invertible, its inverse adding that multiple back. Row zero remains unchanged, and the resulting first column is p followed by zeros. For each j ≠ 0, choose c_j with B_(0,j) = p c_j and subtract c_j times column zero from column j. These operations are also invertible. They clear the first row outside its first entry, and do not change entries below that row because column zero is already zero there. Consequently there are invertible matrices P_0 and Q_0, incorporating the swaps and these operations, such that P_0 D Q_0 is block diagonal with blocks p and an m-by-m matrix D'.

5. An invertible matrix has unit determinant: taking determinants of its product with its inverse gives a multiplicative inverse for its determinant. Hence det(P_0) det(D) det(Q_0) is nonzero. The determinant of the block matrix is p det(D'), so det(D') ≠ 0. The induction hypothesis supplies invertible P' and Q' and nonzero diagonal entries d' with P' D' Q' = diagonal(d').

6. Let L and R be the block matrices diagonal(1,P') and diagonal(1,Q'). Their inverses are diagonal(1,(P')⁻¹) and diagonal(1,(Q')⁻¹), respectively. Set P = L P_0 and Q = Q_0 R. Products of invertible matrices are invertible. Block multiplication gives P D Q = diagonal(p, diagonal(d')). Define d(0) = p and d(i.succ) = d'(i). This block matrix is diagonal(d), and every entry of d is nonzero by the choice of p and the induction hypothesis. This completes the induction and the theorem.

## Key steps

1. Use uniformizer factorizations to obtain divisibility from an inequality of natural exponents.
2. Handle the empty matrix explicitly.
3. Choose a nonzero pivot with minimal exponent and move it to the first diagonal position.
4. Use invertible row and column operations to isolate a one-by-one block.
5. Deduce that the remaining block has nonzero determinant and apply induction.
6. Extend the inductive transformations by identity blocks and compose them.

## Reference use

### local-project

Queries:
- `rg -n 'ord_coe_unit|ord_coe_irreducible|exists_unit_mul_zpow|ord_coe_nonneg|structure Place|def ord|IsDiscreteValuationRing' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_*.lean`
- `rg -n 'length_eq_add_of_exact|length_pi|length_eq_one|length_eq_zero|length.*equiv|length.*quotient|length_prod' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `rg -n 'eq_unit_mul_pow_irreducible|exists_irreducible|class IsDiscreteValuationRing|irreducible.*maximalIdeal|length|cokernel' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/*.lean`
- `rg -n 'length.*det|det.*length|ord.*length|length.*ord|cokernel.*diagonal|diagonal.*cokernel' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra`
- `rg -n 'p06_9e0f5043ff_dlen_(scalar_quotient|matrix_diagonalization|diagonal_cokernel)' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json Definitions Submission.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/FreeModule/PID.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Quotient/Pi.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/OrderOfVanishing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/Submission.frozen-source-check.log`

The project supplies the place DVR instance and normalized order laws. Mathlib supplies unit-times-uniformizer factorization, length_quotient_pow_maximalIdeal, exact-sequence length additivity, LinearEquiv.length_eq, length_pi_of_fintype, submodule Smith normal form, matrix-to-linear-map multiplication, and quotient/product infrastructure. No matching determinant-length or diagonal-cokernel theorem was found. Ring.ord is a different, ENat-valued definition and cannot silently replace the project's integer-valued order. The proposed names have no collision in the inspected DAG or project declarations. Project HEAD and mathlib HEAD match the manifest; mathlib has no tracked modifications, and the seven compared interface files match the snapshot byte-for-byte. Existing audit logs report only propext, Classical.choice and Quot.sound for length_eq_add_of_exact and exists_unit_mul_zpow, but do not certify these new children. No Lean or Lake executable is available in this session. Earlier authoritative Submission checks failed on three unavailable attribute targets. Consequently, fresh elaboration after the authoritative import, inferred-instance checks, complete transitive axiom checks, and comparator acceptance remain unverified activation gates.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/555

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
