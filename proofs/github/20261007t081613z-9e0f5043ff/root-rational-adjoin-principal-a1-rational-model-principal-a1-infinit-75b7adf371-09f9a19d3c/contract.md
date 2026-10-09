<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1 -->

## Theorem `Submission.p06_9e0f5043ff_inf_valuation_fraction_characterization`

Let K and F be fields with a K-algebra structure on F. Suppose s ∈ F is transcendental over K and every f ∈ F has a representation a(s)/b(s) with a,b ∈ K[T] and b ≠ 0. Let w be an AlgebraicCurve.Place K F such that s⁻¹ does not belong to W = w.toValuationSubring. Then, for every f ∈ F, membership f ∈ W is equivalent to the existence of a,b ∈ K[T] such that T does not divide b and f = a(s)/b(s).

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/75

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/259, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/260

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_inf_valuation_fraction_characterization`

```lean
∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F), Transcendental K s → (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧ f = Polynomial.aeval s a / Polynomial.aeval s b) → ∀ w : AlgebraicCurve.Place K F, s⁻¹ ∉ w.toValuationSubring → ∀ f : F, f ∈ w.toValuationSubring ↔ ∃ a b : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ b ∧ f = Polynomial.aeval s a / Polynomial.aeval s b
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

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data and write W = w.toValuationSubring. Transcendence gives s ≠ 0 and nonzero evaluation at s for every nonzero polynomial. The valuation-subring property gives s ∈ W or s⁻¹ ∈ W. The latter is excluded, so s ∈ W. The element s, regarded as an element of W, is not a unit: an inverse in W would, after inclusion into F, equal s⁻¹, contrary to the hypothesis.
2. A project place contains the image of every element of K. Together with s ∈ W and closure under sums and products, this shows that evaluation at s defines a unital ring homomorphism E : K[T] → W. The valuation subring W is a local ring. Let m be its maximal ideal and let J = E⁻¹(m). Since E(1) = 1 and 1 ∉ m, J is proper. Since E(T) = s is a nonunit, s ∈ m, so T ∈ J and (T) ⊆ J.
3. Evaluation at zero maps K[T] surjectively onto K, because it sends C(c) to c. Its kernel is precisely (T): evaluation at zero is the constant coefficient, and a polynomial has zero constant coefficient exactly when it is divisible by T. Hence K[T]/(T) is isomorphic to the field K, so (T) is maximal. The proper ideal J contains (T), and therefore J = (T).
4. If T does not divide a polynomial b, then b ∉ J, so E(b) ∉ m. In a local ring the elements outside the maximal ideal are exactly the units; thus E(b) is a W-unit. For any polynomial a, E(a) belongs to W, and multiplying E(a) by the inverse of E(b) shows that a(s)/b(s) belongs to W. This proves the implication from the stated fraction representation to membership.
5. Conversely, let f ∈ W. If f = 0, choose a = 0 and b = 1. The polynomial T does not divide 1, and 0(s)/1(s) = 0. Now suppose f ≠ 0. The fraction-generation hypothesis supplies a,b with b ≠ 0 and f = a(s)/b(s). Necessarily a ≠ 0; also both evaluations are nonzero by transcendence.
6. Factor out all powers of T from a and b, obtaining a = T^r a₀ and b = T^k b₀, where r,k are natural numbers and T divides neither a₀ nor b₀. Such factorizations exist by repeatedly dividing by T when possible: a nonzero divisible polynomial Tq has q ≠ 0 and degree one greater than q, so this process strictly decreases a natural-number degree and terminates. By step 4, a₀(s) and b₀(s) are W-units. Thus u = a₀(s)/b₀(s) is a W-unit, and evaluation of the factorizations gives f = u s^((r : ℤ)−(k : ℤ)).
7. Suppose r < k. Then n = k−r−1 is a natural number. The elements f, u⁻¹, and s^n all belong to W. Since s ≠ 0 and u ≠ 0, their product in F is f u⁻¹ s^n = s^((r : ℤ)−(k : ℤ)+(n : ℤ)) = s⁻¹. This contradicts s⁻¹ ∉ W. Hence k ≤ r.
8. It follows that f = (T^(r−k)a₀)(s)/b₀(s), and T does not divide b₀. This is the required fraction representation. Together with the zero case and step 4, it proves the equivalence for every f.

## Key steps

1. Put the parameter in the valuation subring and show that it is a nonunit.
2. Contract the maximal ideal along polynomial evaluation.
3. Identify the contraction with the maximal ideal generated by X using evaluation at zero.
4. Show that every permitted denominator evaluates to a unit, proving one implication.
5. Represent a nonzero member as a polynomial fraction and remove all X-factors.
6. Rule out a negative parameter exponent because it would put the inverse parameter in the subring.
7. Construct a fraction with denominator not divisible by X and handle zero separately.

## Reference use

### local-project

Queries:
- `finite_place_model|reverse_eval|eval₂_reverse|eval_reverse|transcendental_inv|transcendental_iff_inv`
- `mem_or_inv_mem|isUnit_iff|eq_of_le_of_ne_top|algebraMap_mem|X_dvd_iff|exists.*pow.*dvd|X_pow|trailingDegree|factor.*X`
- `isMaximal.*X|X.*isMaximal|ker.*eval|span_X|eval.*ker`
- `p06_9e0f5043ff_inf_reciprocal_presentation|p06_9e0f5043ff_inf_reciprocal_polynomial_order|p06_9e0f5043ff_inf_valuation_fraction_characterization`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/Reverse.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/Div.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Polynomial/Ideal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Polynomial/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/name-collision-check.json`

The snapshot supplies Place.ext, Place.ord_mul, Place.ord_zpow, polynomial reversal identities, X-divisibility and root-multiplicity factorization, valuation-subring locality, and the quotient-by-X identification with K. No finite_place_model declaration was found in the snapshot; it is an existing ancestor-level DAG dependency, not an accepted library theorem. Proposed identifiers have no searched-source or active-DAG collisions. Project revision 956e8c600d8b95b46948ae5e37b13930b5f3d06b, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and all nine dependencies match their manifests with clean tracked files. All three proposed types elaborate warning-free under the existing isolated import-only Submission interface. Definitional checks verify the canonical FractionRing algebra, polynomial evaluation, and Place subring and residue algebras. Audited supporting declarations use only propext, Classical.choice, and Quot.sound. However, checking the unchanged actual Submission.lean fails on the pre-existing unknown attribute targets AlgebraicCurve.IsCurveOver.instNontrivialKaehler, AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply, and AlgebraicCurve.SemilinearAut.coe_torsion_smul. Consequently actual import Submission validation remains blocked; interface typechecking is not comparator acceptance or authorization to activate children.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/565

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
