<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1.fraction_extension-a1 -->

## Theorem `Submission.p06_9e0f5043ff_io_fraction_extension`

Let K and F be fields with a K-algebra structure on F. Let x ∈ F be transcendental over K, and assume every f ∈ F equals a(x)/b(x) for polynomials a,b ∈ K[T] with b ≠ 0. Let μ : K[T] → ℕ satisfy μ(ab)=μ(a)+μ(b) for all nonzero a,b. Then there exists ν : F → ℤ such that ν(0)=0, ν(a(x)/b(x))=(μ(a):ℤ)−(μ(b):ℤ) for every nonzero a,b, and ν(f/g)=ν(f)−ν(g) for every nonzero f,g.

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1.fraction_extension-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/124

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_io_fraction_extension`

```lean
∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F), Transcendental K x → (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) → ∀ μ : Polynomial K → ℕ, (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 → μ (a * b) = μ a + μ b) → ∃ ν : F → ℤ, ν 0 = 0 ∧ (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 → ν (Polynomial.aeval x a / Polynomial.aeval x b) = (μ a : ℤ) - (μ b : ℤ)) ∧ (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g)
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

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1.fraction_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Set e = Polynomial.aeval x. Transcendence means that e is injective, so e(a) ≠ 0 exactly when a ≠ 0. For any nonzero f choose a representation f = e(a)/e(b) with b ≠ 0. Its numerator a is nonzero, because a = 0 would give f = 0.
2. Suppose e(a)/e(b) = e(c)/e(t), where all four polynomials are nonzero. The denominators evaluate to nonzero elements, so cross multiplication gives e(a t) = e(c b). Injectivity gives a t = c b. The assumed product rule yields μ(a) + μ(t) = μ(c) + μ(b). Casting this equality into the integers and rearranging proves μ(a) - μ(b) = μ(c) - μ(t), with all differences taken in the integers.
3. Define ν(0) = 0. For each nonzero f use a chosen representation from step 1 and define ν(f) = (μ(a) : ℤ) - (μ(b) : ℤ). Step 2 makes this independent of the choice. In particular, for every nonzero a,b, their evaluated quotient is nonzero, and comparison with its chosen representation proves the required formula for ν(e(a)/e(b)).
4. Let f,g be nonzero, and choose f = e(a)/e(b) and g = e(c)/e(t) with all four polynomials nonzero as in step 1. Field arithmetic and the fact that e respects multiplication give f/g = e(a t)/e(b c). The polynomials a t and b c are nonzero because K[T] is a domain.
5. Apply the formula from step 3 and the product rule for μ to obtain ν(f/g) = (μ(a) : ℤ) + (μ(t) : ℤ) - ((μ(b) : ℤ) + (μ(c) : ℤ)) = ((μ(a) : ℤ) - (μ(b) : ℤ)) - ((μ(c) : ℤ) - (μ(t) : ℤ)) = ν(f) - ν(g). Along with the definition at zero and step 3, this proves the whole conclusion.

## Key steps

1. Use transcendence to obtain injective evaluation and nonzero numerators and denominators.
2. Cross-multiply equal fractions and apply additivity of μ to prove independence of the integer difference.
3. Define ν by chosen representations, with ν(0)=0, and establish its formula for every nonzero polynomial fraction.
4. Represent division using the polynomial products a t and b c.
5. Apply additivity and integer arithmetic to prove the division law.

## Reference use

### local-project

Queries:
- `rg -n 'theorem.*(multiplicity_eq_zero|multiplicity_eq_iff|finiteMultiplicity|exists_eq_pow|multiplicity_one|multiplicity_self|multiplicity_mul)|def multiplicity'`
- `rg -n 'transcendental_iff_injective|theorem.*aeval_injective|finiteMultiplicity_iff|finiteMultiplicity.*not_isUnit|Irreducible.prime'`
- `rg -n 'namespace RationalFunctionField|def heightOneSpectrumOfIrreducible|class HasPrincipalDivisors'`
- `rg -n 'p06_9e0f5043ff_elp_integer_order|p06_9e0f5043ff_io_polynomial_exponent|p06_9e0f5043ff_io_fraction_extension'`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Multiplicity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project`

The snapshot pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Multiplicity.lean provides multiplicity_eq_zero, FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd, multiplicity_mul, and multiplicity_self; Algebraic/Basic.lean provides transcendental_iff_injective. These five declarations were checked transitively and use only propext, Classical.choice, and Quot.sound. Installed dependencies matched their pins and were clean. DivisorClassGroup.lean confirms the unchanged root definition of HasPrincipalDivisors. The helper-name search found no matches in the pinned project; proposed names also had no DAG collisions. Both proposed types elaborated after import Submission using the existing import-only interface. The full frozen Submission still fails on three pre-existing unknown attribute targets, so exact-source validation remains blocked; interface elaboration is not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/470

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
