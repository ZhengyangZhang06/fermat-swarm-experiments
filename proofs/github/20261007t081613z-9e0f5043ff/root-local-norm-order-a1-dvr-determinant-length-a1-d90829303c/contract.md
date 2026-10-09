<!-- theorem-id: fermat-p06/root.local_norm_order-a1.dvr_determinant_length-a1 -->

## Theorem `Submission.p06_9e0f5043ff_lno_dvr_determinant_length`

Let K and E be fields with an algebra structure K → E, let v be a project place of E over K, and put A = v.toValuationSubring. Let M be a finite free A-module and T an A-linear endomorphism with nonzero determinant. There exists n ∈ ℕ such that the A-module length of M/T(M) is n, regarded in ℕ∞, and v.ord of the image of det(T) in E is n, regarded in ℤ.

Node: `root.local_norm_order-a1.dvr_determinant_length-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/36

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/95, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/96, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/97

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_lno_dvr_determinant_length`

```lean
∀ (K E : Type*) [Field K] [Field E] [Algebra K E] (v : AlgebraicCurve.Place K E) (M : Type*) [AddCommGroup M] [Module v.toValuationSubring M] [Module.Free v.toValuationSubring M] [Module.Finite v.toValuationSubring M] (T : M →ₗ[v.toValuationSubring] M), LinearMap.det T ≠ 0 → ∃ n : ℕ, Module.length v.toValuationSubring (M ⧸ LinearMap.range T) = (n : ℕ∞) ∧ v.ord (algebraMap v.toValuationSubring E (LinearMap.det T)) = (n : ℤ)
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
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the hypotheses and write A = O_v. The project place instances make A a proper DVR with fraction field E. Choose a uniformizer π. Every nonzero a ∈ A is uπ^e for an A-unit u and an integer e ≥ 0. The project lemmas ord_coe_unit, ord_coe_irreducible, and exists_unit_mul_zpow identify e with v.ord(a). In particular, among two nonzero elements of A, the one with smaller order divides the one with larger order.

2. We use length additivity for finite-length modules, as provided by Module.length_eq_add_of_exact in the pinned Mathlib/RingTheory/Length.lean. Its elementary chain argument is as follows. In an exact sequence 0 → U → V → W → 0 with finite-length end terms, concatenate a longest chain in U with inverse images of a longest chain in W to obtain a chain of length ℓ(U)+ℓ(W) in V. Conversely, intersect a chain in V with U and take its images in W. At a strict inclusion at least one resulting inclusion is strict: if both were equal, every element in the larger submodule could have its image lifted from the smaller one, and subtraction would place the difference in their common intersection with U. Thus every chain has at most ℓ(U)+ℓ(W) steps. This proves finiteness and additivity, and consequently additivity for finite direct sums.

3. For every a ∈ ℕ, the quotient A/(π^a) has length a. If a = 0 the quotient is zero. Otherwise its filtration by the images of (π^j), for 0 ≤ j ≤ a, has successive factors (π^j)/(π^(j+1)). Multiplication by π^j induces an isomorphism A/(π) → (π^j)/(π^(j+1)): surjectivity follows from the definition of the principal ideal, and injectivity follows by cancelling the nonzero π^j in the domain A. Each factor is the residue field, which is a simple A-module. Applying step 2 repeatedly gives the asserted length.

4. Choose a finite A-basis of M and let D be the square matrix of T. Its determinant is det(T). If the basis is empty, M is zero, det(T) = 1, and the desired witness is n = 0. Assume henceforth that the matrix has positive size. Its nonzero determinant ensures that it has a nonzero entry.

5. Choose a nonzero entry p having minimum order among the finitely many nonzero entries and move it to the first diagonal position by row and column swaps. By step 1, p divides every entry, including the zero entries. For each subsequent row, subtract the appropriate multiple of the first row to clear the first column. Then subtract appropriate multiples of the first column from the other columns to clear the first row. These operations are invertible over A. The result is block diagonal with blocks p and D′. Its determinant is p det(D′), and is nonzero because every operation multiplies the original determinant by a unit. Since A is a domain, det(D′) is nonzero.

6. Induct on matrix size using step 5. The result is a diagonal matrix with nonzero entries d_i. Write d_i = u_i π^(a_i), with u_i an A-unit and a_i ∈ ℕ. Every row or column operation used has unit determinant, so the determinant order of the original matrix equals the order of the product of the d_i. The normalized order laws therefore give v.ord(det(T)) = ∑_i a_i, with det(T) viewed in E.

7. Right multiplication by an invertible matrix does not change the image of the associated linear map. Left multiplication carries that image by an automorphism of its codomain, and hence induces an isomorphism of cokernels. Thus M/T(M) is A-linearly isomorphic to the cokernel of the diagonal matrix, namely the finite direct sum of A/(d_i). Because u_i is a unit, (d_i) = (π^(a_i)). Steps 2 and 3 give length_A(M/T(M)) = ∑_i a_i.

8. Set n = ∑_i a_i. Step 7 gives the required equality in ℕ∞, and step 6 gives the required equality in ℤ. This proves both conclusions with the same natural number n.

## Key steps

1. Use the normalized DVR order to turn order comparisons into divisibility.
2. Compute the length of A/(π^a) from its residue-field filtration.
3. Diagonalize a nonsingular matrix by invertible row and column operations.
4. Identify its cokernel with a direct sum of principal-power quotients.
5. Compute both determinant order and cokernel length as the sum of the diagonal exponents.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
