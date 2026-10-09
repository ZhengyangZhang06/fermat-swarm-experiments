<!-- theorem-id: fermat-p06/root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1 -->

## Theorem `Submission.p06_9e0f5043ff_wll_local_length_multiplicity`

Let B be a commutative Dedekind domain and b ∈ B. Set C = B/bB. Let s be a B-composition series of C from zero to C and let p : Fin(s.length) → HeightOneSpectrum B. Suppose each successive quotient s(i+1)/s(i), formed using the canonical inclusion, is B-linearly isomorphic to B/p(i).asIdeal. For every q ∈ HeightOneSpectrum B, put R_q = Localization.AtPrime q.asIdeal. Then length_{R_q}(R_q/(image(b))) equals, in ℕ∞, the natural-number cardinality of {i : Fin(s.length) | p(i) = q}. All quotient and localization actions are canonical. No additional assumption b ≠ 0 is needed once the specified series and factors are supplied.

Node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/76

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/146, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/147

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_wll_local_length_multiplicity`

```lean
∀ (B : Type*) [CommRing B] [IsDedekindDomain B] (b : B) (s : CompositionSeries (Submodule B (B ⧸ Ideal.span ({b} : Set B)))) (p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B), s.head = ⊥ → s.last = ⊤ → (∀ i : Fin s.length, Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B] (B ⧸ (p i).asIdeal))) → ∀ q : IsDedekindDomain.HeightOneSpectrum B, Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⧸ Ideal.span ({algebraMap B (Localization.AtPrime q.asIdeal) b} : Set (Localization.AtPrime q.asIdeal))) = (Nat.card {i : Fin s.length // p i = q} : ℕ∞)
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

- Parent DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1`
- Child DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix q, let T = B \ q.asIdeal, and put R = T⁻¹B. Localization at T preserves short exact sequences. Indeed, for an exact sequence with maps f and g, if g(x)/s = 0, the zero-fraction criterion supplies t ∈ T with g(tx) = 0. Exactness supplies y with f(y) = tx, and then y/(ts) maps to x/s. This proves exactness in the middle; the reverse inclusion follows from g ∘ f = 0. If f is injective and f(x)/s = 0, some t ∈ T satisfies f(tx) = 0, hence tx = 0 and x/s = 0. Surjectivity after localization follows by lifting each numerator. These arguments also show that the induced maps are R-linear.

2. The quotient map B → C induces a surjective R-linear map R → T⁻¹C taking a/s to the fraction of the class of a. Its kernel consists of those a/s for which some t ∈ T satisfies ta ∈ bB. If ta = bd, then a/s = image(b)·(d/(ts)), so this fraction lies in image(b)R. Conversely every multiple of image(b) maps to zero because b annihilates C. Thus the kernel is precisely image(b)R, and the quotient map induces an R-linear isomorphism R/image(b)R ≃ T⁻¹C.

3. Write N_j for the terms of s and Q_i = N_{i+1}/N_i for its successive quotients. Applying step 1 to their short exact sequences and to the injections N_j → C identifies T⁻¹N_j with an increasing chain of R-submodules of T⁻¹C. This chain starts at zero and ends at T⁻¹C. Its successive quotient at i is R-linearly isomorphic to T⁻¹Q_i, and the supplied factor isomorphism identifies this with T⁻¹(B/p(i).asIdeal).

4. Suppose p(i) ≠ q, and set r = p(i).asIdeal. Height-one primes of a Dedekind domain are maximal, and equality of their underlying ideals implies equality of the points. Thus r and q.asIdeal are distinct maximal ideals. There exists t ∈ r outside q.asIdeal: otherwise r would be contained in q.asIdeal, forcing equality by maximality. This t annihilates B/r and becomes a unit in R. Therefore every element of T⁻¹(B/r) is zero, because multiplying it by t gives zero and multiplication by t is invertible.

5. Suppose p(i) = q. The quotient k = B/q.asIdeal is a field. Every denominator t ∈ T has a nonzero, hence invertible, class in k. The map T⁻¹k → k sending u/t to u·(t mod q)⁻¹ is well-defined: equality of fractions becomes equality after multiplying by a class from T, which is invertible in k. Its inverse is u ↦ u/1. Give k the R-action in which a/s acts by multiplication by (a mod q)/(s mod q); the two maps are R-linear inverses. Any R-submodule of k is in particular a B-submodule, and B → k is surjective, so it is an ideal of the field k. Hence k is a nonzero simple R-module. Thus precisely the indices with p(i) = q give nonzero localized successive quotients, and each such quotient is simple.

6. Let c be the cardinality of the finite subtype {i : Fin(s.length) | p(i) = q}. By steps 3–5, the localized chain has equal adjacent terms exactly at the indices not counted by c. Delete these repetitions. Every retained transition corresponds to one of the c nonzero successive quotients: intervening deleted terms are equal submodules, so deleting them does not change that transition’s quotient. The resulting chain therefore has exactly c strict steps, all with simple successive quotients, and retains the endpoints zero and T⁻¹C. It is a composition series of length c. If c = 0, all terms of the localized chain coincide, so T⁻¹C = 0 and the resulting series has length zero.

7. Module.length_compositionSeries gives length_R(T⁻¹C) = (c : ℕ∞). Transfer this equality along the R-linear isomorphism in step 2. Since c is Nat.card of the finite subtype in the statement and R is the specified localization at q, the transferred equality is exactly the required local quotient length formula.

## Key steps

1. Prove exactness, injectivity preservation, and surjectivity preservation for localization by fractions.
2. Identify the localized principal quotient with R_q/image(b)R_q by computing the kernel.
3. Localize the given series and its factor isomorphisms.
4. Kill factors belonging to other maximal ideals using an inverted annihilator.
5. Identify the q-factors with a simple residue-field module.
6. Delete repeated terms and count the remaining composition factors.
7. Apply composition-series length and transfer through the quotient isomorphism.

## Reference use

### local-project

Queries:
- `rg -n 'length_compositionSeries|length_eq_add_of_exact|hasPrincipalDivisors_of_transcendental|length.*localiz|localiz.*length' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`
- `rg -n 'length.*(sum|localiz)|sum.*length|localiz.*length' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Localization .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain`
- `rg -n 'isFiniteLength_iff_exists_compositionSeries|isFiniteLength_of_exists_compositionSeries' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/FiniteLength.lean`
- `rg -n 'p06_9e0f5043ff_wll_residue_composition_series|p06_9e0f5043ff_wll_length_sum_factors|p06_9e0f5043ff_wll_local_length_multiplicity' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json Submission.lean Definitions Fermat`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/FiniteLength.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/SimpleModule/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Module/LocalizedModule/Exact.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-lengths-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-lengths-a1/decomposition-typecheck/LocalizationAxioms.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-lengths-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-lengths-a1/decomposition-typecheck/provenance-check.json`

The snapshot supplies composition-series existence, classification of simple modules by maximal-ideal quotients, length additivity, exact localization, and maximality of height-one primes. The focused weighted-localization-length search returned no matches. Project revision 956e8c600d8b95b46948ae5e37b13930b5f3d06b and all nine clean pinned dependencies match their recorded revisions, including mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Inspected library sources match the snapshot. Audited declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. No proposed-name collisions were found. All three types and canonical quotient scalar-action checks pass after import Submission in the existing import-only interface. However, the unchanged authoritative Submission still fails on three inherited unknown attribute targets; authoritative import validation remains required before child proof work begins. No comparator acceptance is claimed.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
