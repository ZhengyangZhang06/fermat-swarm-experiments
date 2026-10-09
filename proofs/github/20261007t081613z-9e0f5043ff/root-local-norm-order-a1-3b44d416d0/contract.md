<!-- theorem-id: fermat-p06/root.local_norm_order-a1 -->

## Theorem `Submission.p06_9e0f5043ff_local_norm_order`

Let K, E and L be fields with compatible algebra structures forming a scalar tower K → E → L, and suppose L/E is finite-dimensional and separable. For every project place v of E over K and every nonzero f in L, ord_v(Norm_{L/E}(f)) equals the sum over the finite set v.fiberOver L of inertiaDeg_E(w) times ord_w(f). Here inertiaDeg_E(w) is the natural-number finrank of κ(w) over κ(w.restrict E), using the project's canonical residue-field algebra, and it is cast to an integer in the sum. No principal-divisor hypothesis is assumed.

Node: `root.local_norm_order-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/57, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/58, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/59

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_local_norm_order`

```lean
∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FiniteDimensional E L] [Algebra.IsSeparable E L] (v : AlgebraicCurve.Place K E) (f : L), f ≠ 0 → v.ord (Algebra.norm E f) = Finset.sum (v.fiberOver L) (fun w => (w.inertiaDeg E : ℤ) * w.ord f)
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

- Parent DAG node: `root`
- Child DAG node: `root.local_norm_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the tower, v and f ≠ 0. Set A = O_v, let π be a uniformizer, and let k_v = A/(π). By the definition and instances of a project place, A is a proper DVR with fraction field E. Its normalized order counts uniformizer exponents: every nonzero element of E is uπ^m with u an A-unit, and ord_v(uπ^m) = m. These assertions are the existing project uniformizer factorization and order lemmas.

2. Let B be the integral closure of A in L and put n = [L:E]. Apply the pinned IsIntegralClosure.finite, IsIntegralClosure.module_free, IsIntegralClosure.rank, IsIntegralClosure.isFractionRing_of_finite_extension and IsIntegralClosure.isDedekindDomain from mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean. Their hypotheses hold: A is a Noetherian integrally closed PID, E is its fraction field, L/E is finite separable, and the injective maps into the fields give torsion-freeness and compatible scalar towers. Therefore B is a finite free A-module of rank n, is a Dedekind domain, and has fraction field L.

3. An A-basis of B is also an E-basis of L. For spanning, take z in L and a monic equation z^m + ∑_{i<m} c_i z^i = 0 over E. Choose nonzero d in A clearing all coefficient denominators. Multiplication of the equation by d^m shows that dz is integral over A, because its coefficients c_i d^(m−i) lie in A. Thus dz belongs to B, and z = d⁻¹(dz) lies in the E-span of B. For independence, multiply an E-linear relation among the A-basis elements by a common nonzero denominator from A; A-linear independence makes every coefficient zero.

4. Every maximal ideal q of B is nonzero and lies above (π). Indeed, B ∩ E = A by integral closedness of A. If B were a field, it would contain π⁻¹, contradicting this equality. Thus a maximal ideal q cannot be zero. Choose nonzero b in q and a monic equation for b over A of least degree. Its constant coefficient c_0 is nonzero, since otherwise cancellation of b gives a shorter monic equation. The equation puts c_0 in q ∩ A. This contraction is consequently a nonzero prime of the DVR A and equals (π).

5. The set Q of maximal ideals of B is finite, and each B/q is finite-dimensional over k_v. Since B is free of rank n over A, B/πB has dimension n over k_v. Each B/q is its nonzero field quotient and thus has finite dimension f_q ≥ 1. For any r distinct maximal ideals q_1,…,q_r, pairwise comaximality gives a surjection B/πB → ∏_i B/q_i. Explicitly, for each pair i ≠ j choose an element of q_j congruent to 1 modulo q_i; products over j give selectors, and sums of selector multiples lift arbitrary tuples. Consequently r ≤ ∑_i f_(q_i) ≤ n. There cannot be n+1 distinct maximal ideals, so Q is finite.

6. For each q in Q, its localization B_q is a DVR with fraction field L. This follows from the pinned IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain in mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean, since B is Dedekind and q is nonzero. Regard B_q inside L. It contains A and hence K. It is a proper principal valuation subring and therefore defines a project place. Its intersection with E equals A: if it contained z = uπ^(−r) outside A, where u is an A-unit and r > 0, it would contain π⁻¹. This contradicts π lying in its maximal ideal qB_q. Thus this place restricts to v.

7. Conversely, let w restrict to v. Since A is contained in O_w and every element of B is integral over A, the project's integral-root lemma puts B inside O_w. Let q = B ∩ m_w. It is prime and contains π: the restriction order identity gives ord_w(π) = e_w > 0. Thus q is a nonzero prime of the Dedekind domain B, hence maximal. Every element of B outside q is a unit in O_w, so B_q is contained in O_w. A proper overring of a DVR inside its fraction field equals that DVR: an element uτ^(−r) outside the DVR would put τ⁻¹ in the overring, and then all fraction-field elements belong to it. Hence O_w = B_q. These constructions are inverse, because the maximal ideal of B_q contracts to q and equality of valuation rings gives equality of project places. This is also the correspondence implemented by Place.fiberEquiv.

8. The residue field of B_q is B/q. Reduction is well-defined on localized fractions because every denominator outside q has invertible image in B/q; it is surjective with kernel qB_q. Under step 7 this identifies κ(w) with B/q. The map from k_v is reduction of the inclusion A → B_q, exactly the residue map defining the project's restriction algebra. Consequently f_q = Module.finrank k_v (B/q) equals w.inertiaDeg E for the corresponding w. The normalized order ν_q of B_q likewise equals w.ord, since both assign 1 to a uniformizer and 0 to units.

9. Establish the length facts needed in the determinant calculation. For a finite-length module, its length is the maximum number of strict steps in a submodule chain. A longest chain has simple factors, because any nonsimple factor would permit refinement. In an exact sequence 0 → U → V → W → 0 with finite-length end terms, concatenating a longest chain in U with preimages of a longest chain in W gives length(V) ≥ length(U) + length(W). Conversely, intersect any chain in V with U and take its images in W. At every strict step at least one of these chains increases strictly: equality of both intersection and image lets one subtract a lift in the smaller submodule and proves equality of the original two submodules. This bounds every chain by length(U) + length(W), establishing finite length and equality. It also proves that any composition series has as many factors as the module's length.

10. Let T be an endomorphism of a finite free A-module with nonzero determinant. Its cokernel has length ord_v(det T). To prove this, represent T by a square matrix. Rank zero gives determinant 1 and zero cokernel. At positive rank choose a nonzero entry of least order and move it to the first diagonal position. It divides every entry in A, so invertible row operations clear its column and invertible column operations clear its row. The remaining block has nonzero determinant. Induction gives a diagonal matrix with entries u_iπ^(a_i), where each u_i is a unit and each a_i is nonnegative. These operations preserve the cokernel up to isomorphism and multiply the determinant by a unit. The cokernel is the direct sum of A/(π^(a_i)). The powers-of-π filtration of each such quotient has a_i factors isomorphic to A/(π); for a_i = 0 it is zero. Step 9 therefore gives cokernel length ∑_i a_i, while normalized order gives precisely the same value for the determinant.

11. Apply step 10 to multiplication by a nonzero b in B on the free A-module B. By step 3 the same matrix describes multiplication by b on the E-vector space L. Its determinant, viewed in E, is Norm_{L/E}(b), by Algebra.norm_apply. This determinant is nonzero because multiplication by b on L is invertible. Consequently ord_v(Norm(b)) = length_A(B/bB).

12. Put C = B/bB. Its A-length is finite by step 11. Every chain of B-submodules is a chain of A-submodules, so a B-submodule chain of maximum length exists and is a finite composition series. Each simple B-factor is B/q for a maximal ideal q: a nonzero element generates the simple module, and the kernel of B mapping onto it is maximal. Let c_q count its factors isomorphic to B/q. The A-action on B/q factors through k_v, and its A-submodules are exactly its k_v-linear subspaces. Its A-length is therefore its dimension f_q. Additivity from step 9 yields length_A(C) = ∑_{q∈Q} c_q f_q.

13. Localize this composition series at a fixed q. Localization is exact: a fraction whose image is zero has a numerator whose image is killed by an allowed denominator; multiplication by that denominator puts the numerator in the original kernel, and exactness there supplies a preimage after division by the enlarged denominator. The same fraction criterion proves preservation of injectivity, and surjectivity follows by lifting numerators. If r ≠ q are maximal, an element of r outside q annihilates B/r and becomes invertible, so (B/r)_q = 0. A factor B/q becomes the residue field of B_q and remains simple. Removing repeated terms in the localized chain shows that c_q = length_{B_q}(B_q/bB_q). Write b = uτ^m in the DVR B_q, with u a unit and m = ν_q(b) ≥ 0. Its powers-of-τ filtration has exactly m residue-field factors. Thus c_q = ν_q(b).

14. Combining steps 11–13 gives ord_v(Norm(b)) = ∑_{q∈Q} f_q ν_q(b) for every nonzero b in B. The finite sum and its coefficients were established locally; no global product formula or principal-divisor theorem has been used.

15. Since L is the fraction field of B, write the given f as b/c with b,c in B nonzero. Norm is multiplicative, since multiplication maps compose and determinants multiply; it is nonzero on nonzero elements because their multiplication maps are invertible. The order laws therefore give ord_v(Norm(f)) = ord_v(Norm(b)) − ord_v(Norm(c)). Apply step 14 to b and c and subtract the finite sums over Q. The order laws in B_q give ν_q(b) − ν_q(c) = ν_q(f). Hence ord_v(Norm(f)) = ∑_{q∈Q} f_q ν_q(f).

16. Reindex this finite sum by the bijection of steps 6–7. By definition and Place.mem_fiberOver, its target is precisely v.fiberOver L. Step 8 identifies f_q with w.inertiaDeg E and ν_q(f) with w.ord f. Viewing the natural-number residue degrees as integers gives exactly the stated Finset.sum identity, with no ramification factor.

## Key steps

1. Normalize the downstairs DVR in the finite separable extension and obtain a finite free Dedekind domain.
2. Show its maximal ideals form a finite set and have finite residue extensions.
3. Identify those maximal ideals and their localizations with exactly the project-place fiber, including canonical residue maps and orders.
4. Prove length additivity and the determinant–cokernel-length identity over a DVR.
5. Interpret the norm of an integral element as the determinant of multiplication on the normalization.
6. Compute the cokernel length by localizing a composition series, obtaining residue degrees times local orders.
7. Extend from integral elements to arbitrary nonzero fractions using multiplicativity.
8. Reindex by fiberOver and identify the coefficients with inertiaDeg.

## Reference use

### local-project

Queries:
- `rg -n 'finite_setOf_restrict_eq|inertiaDeg|PushforwardNormFormula|RatFunc' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions`
- `grep -nE 'residueDegree|FiniteResidue|finrank|ord_norm|norm.*ord|finite.*support|finite.*ord|hasPrincipalDivisors|congrEquiv|congr.*ord' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_*.lean`
- `grep -R -nE 'RatFunc|congrEquiv|congrRingEquiv' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions | head -50`
- `grep -R -nE 'norm.*(valuation|intValuation)|valuation.*norm' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/NumberTheory/RamificationInertia`
- `sed -n '165,230p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `grep -nE 'traceForm_nondegenerate|isIntegral_trace' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Trace/Basic.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Trace/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Norm/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/FieldTheory/Separable.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/CheckTypes.interface-check.log`

The requested rg query failed because rg is unavailable; grep searches were used instead. DivisorClassGroup supplies the exact place, order, divisor and HasPrincipalDivisors definitions and normalized uniformizer factorization. DivisorPushPull supplies restriction, the canonical residue algebra, inertiaDeg, the residue-degree tower identity, and degree_pushforward. PlacesOverDVR supplies the integral-root lemma and finite fibers without assuming HasPrincipalDivisors upstairs. No rational-function transport infrastructure matched the search of project/Definitions, and no valuation-of-norm identity matched the searched mathlib DedekindDomain and RamificationInertia directories. The normalization and localization theorems support the local norm proof. Project HEAD matches 956e8c600d8b95b46948ae5e37b13930b5f3d06b; all nine dependencies are clean at their manifest revisions, including mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Byte-identical copies of the three imported project modules compiled. The audited imported lemmas have only propext, Classical.choice and Quot.sound as transitive axioms. All proposed types and the canonical residue-algebra checks pass under an isolated import-only Submission module containing the exact frozen import. The unchanged original Submission fails on three pre-existing attribute directives referring to unavailable declarations; its failure log is preserved. Thus validation against an unchanged, successfully importing Submission remains an activation gate. No comparator acceptance is claimed.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/762

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
