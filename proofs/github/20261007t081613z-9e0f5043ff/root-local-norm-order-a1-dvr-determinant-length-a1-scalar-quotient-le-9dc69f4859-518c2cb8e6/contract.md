<!-- theorem-id: fermat-p06/root.local_norm_order-a1.dvr_determinant_length-a1.scalar_quotient_length_order-a1 -->

## Theorem `Submission.p06_9e0f5043ff_dlen_scalar_quotient`

Let K and E be fields with an algebra structure K → E, let v : AlgebraicCurve.Place K E, and write A = v.toValuationSubring. For every nonzero a ∈ A, there exists n ∈ ℕ such that length_A(A/(a)) = n in ℕ∞ and v.ord(algebraMap A E a) = n in ℤ.

Node: `root.local_norm_order-a1.dvr_determinant_length-a1.scalar_quotient_length_order-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/57

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_dlen_scalar_quotient`

```lean
∀ (K E : Type*) [Field K] [Field E] [Algebra K E] (v : AlgebraicCurve.Place K E) (a : v.toValuationSubring), a ≠ 0 → ∃ n : ℕ, Module.length v.toValuationSubring (v.toValuationSubring ⧸ Ideal.span ({a} : Set v.toValuationSubring)) = (n : ℕ∞) ∧ v.ord (algebraMap v.toValuationSubring E a) = (n : ℤ)
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
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.scalar_quotient_length_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, E, v and a with a ≠ 0, and write A = v.toValuationSubring. The project instance makes A a discrete valuation ring. By IsDiscreteValuationRing.exists_irreducible, choose an irreducible π ∈ A. By IsDiscreteValuationRing.eq_unit_mul_pow_irreducible, choose n ∈ ℕ and u ∈ Aˣ with a = uπ^n. Here π ≠ 0, and (π) is the maximal ideal of A.

2. We verify the scalar length calculation. Put Q_j = A/(π^j) for j ∈ ℕ. Since π^0 = 1, Q_0 is the zero module and has length zero. The quotient A/(π) is a simple A-module: its submodules correspond to ideals containing the maximal ideal (π), so only zero and the whole quotient occur, and the quotient is nonzero. Its length is therefore one.

3. For each j ∈ ℕ, multiplication by π^j defines an A-linear map α_j : A/(π) → Q_(j+1), and reduction defines an A-linear map β_j : Q_(j+1) → Q_j. The first map is well-defined because π^j(π) ⊆ (π^(j+1)). It is injective: if π^j x = π^(j+1)y, cancellation of the nonzero π^j gives x = πy. The second map is well-defined and surjective because (π^(j+1)) ⊆ (π^j). Its kernel consists exactly of classes represented by π^j y, which is the image of α_j. Thus these maps form a short exact sequence.

4. Apply Module.length_eq_add_of_exact to this sequence. It gives length_A(Q_(j+1)) = 1 + length_A(Q_j). Induction starting at Q_0 proves length_A(Q_j) = j in ℕ∞ for every j. This is also the specialization of the pinned length_quotient_pow_maximalIdeal theorem using (π^j) = (π)^j.

5. Since u is a unit, (a) = (π^n): one inclusion follows from a = uπ^n and the other from π^n = u⁻¹a. Hence A/(a) and Q_n are the same quotient after this ideal equality, so length_A(A/(a)) = n.

6. The inclusion A → E is injective, so the images of u and π are nonzero. The project laws give order zero for the image of u and order one for the image of π. Repeated application of ord_mul, starting with ord_one, gives order n for the image of π^n. Applying ord_mul once more to a = uπ^n yields v.ord(algebraMap A E a) = 0 + n = n in ℤ. This n proves both required equalities.

## Key steps

1. Factor the nonzero scalar as a unit times a natural power of a uniformizer.
2. Identify the uniformizer quotient as a simple module of length one.
3. Construct and verify the short exact sequence connecting successive power quotients.
4. Induct using length additivity to compute every power-quotient length.
5. Remove the unit from the principal ideal and compute the normalized order of the same factorization.

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

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/297

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
