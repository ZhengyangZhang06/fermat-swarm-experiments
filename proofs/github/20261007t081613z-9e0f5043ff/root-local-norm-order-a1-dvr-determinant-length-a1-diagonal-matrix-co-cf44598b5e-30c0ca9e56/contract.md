<!-- theorem-id: fermat-p06/root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1.diagonal_cokernel_product-a1 -->

## Theorem `Submission.p06_9e0f5043ff_dmc_diagonal_quotient`

Let R be a commutative ring, m a natural number, and d : Fin m → R. The quotient of Fin m → R by the image of column multiplication by diagonal(d) is R-linearly isomorphic to the product, over i : Fin m, of R/Ideal.span({d(i)}). No entry of d is required to be nonzero.

Node: `root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1.diagonal_cokernel_product-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/97

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_dmc_diagonal_quotient`

```lean
∀ (R : Type*) [CommRing R] (m : ℕ) (d : Fin m → R), Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d))) ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R)))
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

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1.diagonal_cokernel_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix R, m and d. Write V = R^(Fin m), I_i = Ideal.span({d(i)}), W = ∏_i R/I_i, and N = image(diagonal(d)). Multiplication by diagonal(d) sends z ∈ V to the vector whose i-th coordinate is d(i)z(i).
2. Define C : V → W by C(y)(i) = [y(i)] modulo I_i. Each coordinate quotient map preserves addition and scalar multiplication, so C is R-linear.
3. If y ∈ N, choose z with y = diagonal(d)z. Then y(i) = d(i)z(i) belongs to I_i for every i. Hence every coordinate of C(y) is zero, proving N ⊆ ker(C).
4. Conversely, if C(y) = 0, then y(i) ∈ I_i for every i. The principal ideal I_i consists exactly of the multiples of d(i): these multiples form an ideal containing d(i), and every ideal containing d(i) contains all its multiples. Consequently, choose z(i) with y(i) = d(i)z(i) for each i, using commutativity if the multiple is initially written in the opposite order. Assemble these witnesses into z ∈ V. The coordinate formula in step 1 gives y = diagonal(d)z, so y ∈ N. Therefore ker(C) = N.
5. The map C is surjective. Given w ∈ W, choose a representative y(i) ∈ R for each quotient class w(i), and assemble them into y ∈ V. Then C(y) = w by equality of all coordinates.
6. Define the induced map C̄ : V/N → W by C̄([y]) = C(y). If two representatives differ by an element of N, their C-images differ by zero by step 3; thus C̄ is well-defined. The addition and scalar identities for C descend to C̄, so C̄ is linear.
7. If C̄([y]) = C̄([z]), linearity gives C(y − z) = 0. Step 4 yields y − z ∈ N, hence [y] = [z]. Thus C̄ is injective. Step 5 gives surjectivity by taking the class of a representative preimage.
8. Let G assign to each element of W its unique preimage under C̄. For w and w' in W, linearity gives C̄(G(w) + G(w')) = w + w', so uniqueness implies G(w + w') = G(w) + G(w'). Similarly C̄(rG(w)) = rw implies G(rw) = rG(w). Thus G is linear and is inverse to C̄, providing the required linear equivalence and Nonempty witness. When m = 0, all coordinate choices and coordinate equalities are empty and the same construction applies.

## Key steps

1. Construct the coordinatewise quotient linear map.
2. Show the diagonal image lies in its kernel.
3. Use principal-ideal membership witnesses to prove the reverse kernel inclusion.
4. Choose coordinate representatives to prove surjectivity.
5. Descend to the quotient by the diagonal image.
6. Prove the induced map is bijective and its inverse is linear.

## Reference use

### local-project

Queries:
- `rg -n --glob '*.lean' 'cokernel.*(isUnit|IsUnit|diagonal)|[Dd]iagonal.*[Cc]okernel|[Cc]okernel.*[Dd]iagonal|range_mulVecLin.*pi|mulVecLin.*quot' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`
- `rg -n 'quotientEquiv|quotEquivOfEq|mapQ' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`
- `rg -n 'span_singleton|mk_surjective|eq_zero_iff_mem' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Quotient/Defs.lean .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Span.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Quotient/Pi.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Isomorphisms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Span.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Quotient/Defs.lean`

No exact matrix-cokernel theorem matched the targeted search. Relevant infrastructure includes Matrix.mulVecLin_mul, Matrix.toLinearEquiv', Submodule.Quotient.equiv, Submodule.quotientPi, LinearMap.quotKerEquivOfSurjective, and principal-ideal membership and quotient-surjectivity lemmas. Inspected sources match installed mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all installed dependencies matched their pins and had clean tracked files. Transitive axiom checks of these library declarations reported only propext, Classical.choice, and Quot.sound. Both proposed types elaborated with Lean 4.33.1 through the existing import-only Submission interface; matrix instances synthesized as Matrix.semiring.toMonoid and Matrix.instMulOfFintypeOfAddCommMonoid. The full frozen Submission has pre-existing unknown attribute targets, so this interface check is not full-contract or comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/299

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
