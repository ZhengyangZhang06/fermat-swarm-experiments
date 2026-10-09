<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1 -->

## Theorem `Submission.p06_9e0f5043ff_rmp_finite_place_model`

Let K and F be fields with a K-algebra structure on F. Let x ∈ F be transcendental over K, and assume every f ∈ F can be written a(x)/b(x) for polynomials a,b ∈ K[T] with b ≠ 0. For every monic irreducible q ∈ K[T], there exists a project place v of F over K such that: f belongs to its valuation subring exactly when f = a(x)/b(x) with q not dividing b; v.deg = q.natDegree; v.ord(q(x)) = 1; and v.ord(a(x)) = 0 whenever q does not divide a.

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/43

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/106, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/108, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/110

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_rmp_finite_place_model`

```lean
∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F), Transcendental K x → (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) → ∀ q : Polynomial K, q.Monic → Irreducible q → ∃ v : AlgebraicCurve.Place K F, (∀ f : F, f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K, ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) ∧ v.deg = q.natDegree ∧ v.ord (Polynomial.aeval x q) = 1 ∧ (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0)
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

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated fields, algebra, generator x, fraction representations, and monic irreducible q. Put R = K[T] and write a(x) for evaluation. Transcendence makes evaluation R → F injective. Since q is irreducible, it is nonzero, is not a unit, and has positive degree. The Euclidean algorithm shows that if q does not divide a, there are u,v ∈ R with uq + va = 1: the greatest common divisor of q and a must be a unit. Multiplying this identity by b proves that q divides ab only if q divides a or b. Thus q is prime.
2. For each nonzero a ∈ R, repeatedly divide out q while possible. Each division decreases degree by the positive integer deg q, so the process terminates and yields a = q^m a₀ with m ∈ ℕ and q not dividing a₀. The exponent m is unique: two unequal exponents would, after cancellation, force q to divide one of the corresponding remaining factors. Denote it by μ(a). Primality shows that the product of two remaining factors is still not divisible by q, hence μ(ab) = μ(a) + μ(b) for nonzero a,b.
3. For nonzero f ∈ F, choose f = a(x)/b(x) with b ≠ 0. Injectivity and f ≠ 0 imply a ≠ 0. Define ν(f) = μ(a) − μ(b) ∈ ℤ. If also f = c(x)/d(x), cross multiplication and injectivity give ad = cb in R. Additivity of μ therefore proves representation independence. It also proves ν(fg) = ν(f) + ν(g) and ν(f⁻¹) = −ν(f) for nonzero f,g.
4. Let A be the set of fractions a(x)/b(x) with q not dividing b. Such denominators are nonzero. The representations with denominator 1 give zero, one, and every element of K. Negatives preserve permitted denominators; addition and multiplication use the product of two permitted denominators, which remains permitted by primality. Thus A is a subring containing K. Factoring q out of a and b writes every nonzero f as u q(x)^n, where n = ν(f), and u and u⁻¹ belong to A. The definition of ν shows that membership in A implies n ≥ 0. Conversely, when n ≥ 0 the displayed expression has a denominator not divisible by q, so f belongs to A. Thus f ∈ A exactly when ν(f) ≥ 0, and a nonzero element of A is a unit exactly when its exponent is zero.
5. Either ν(f) or −ν(f) is nonnegative, so either f or f⁻¹ belongs to A; zero already belongs to A. Hence A is a valuation subring. It is proper because ν(q(x)⁻¹) = −1. Every ideal of A is principal: the zero ideal is generated by zero; in a nonzero ideal choose a nonzero h whose nonnegative exponent is least. For any nonzero z in the ideal, ν(z/h) ≥ 0, so z/h ∈ A and z is a multiple of h. Zero is also a multiple of h. These inclusions identify the ideal with hA.
6. The element π = q(x) belongs to A and has exponent one. It is not a unit. If π = yz in A, both factors are nonzero and their nonnegative exponents sum to one, so one factor has exponent zero and is a unit. Thus π is irreducible in A. The valuation subring A, its inclusion of K, its properness, and its principal-ideal property define a project place v. The project's normalized uniformizer formula gives v.ord(q(x)) = 1. If q does not divide a, then a ≠ 0 and a(x) is an A-unit, so Place.ord_coe_unit gives v.ord(a(x)) = 0.
7. The quotient k = R/(q) is a field: for any nonzero residue class represented by a, the Bezout identity from step 1 supplies its inverse. Define A → k by a(x)/b(x) ↦ ā b̄⁻¹. The denominator has nonzero residue. Cross multiplication proves independence of the representation and verifies addition and multiplication. Constants are preserved, so this is a K-algebra homomorphism. It is surjective because each residue class has a polynomial representative with denominator 1. Its kernel consists exactly of fractions with numerator divisible by q, namely q(x)A. By step 4, these are exactly zero and the nonunits of A, so this kernel is the maximal ideal. Therefore the induced map identifies v.ResidueField with k as a K-algebra.
8. Put d = q.natDegree. Division by the monic polynomial q shows that the classes of 1,T,…,T^(d−1) span k. A linear relation among these classes is represented by a polynomial of degree less than d that is divisible by q. A nonzero multiple of q has degree at least d, so that representative must be zero, and all coefficients of the relation vanish. These classes form a basis. Consequently dim_K k = d and v.deg = d. Together with the defining membership characterization of A and step 6, this proves every required conclusion.

## Key steps

1. Use Euclidean division and Bezout to obtain primality and finite q-multiplicities.
2. Define the representation-independent integer exponent on nonzero fractions.
3. Identify localization membership and units by the sign and vanishing of the exponent.
4. Prove proper valuation-subring and principal-ideal properties, then construct the project place.
5. Normalize order using the irreducible uniformizer q(x).
6. Identify the residue field with K[T]/(q) and compute its dimension by the remainder basis.

## Reference use

### local-project

Queries:
- `HasPrincipalDivisors|namespace RationalFunctionField|structure Place|def ord|def deg|ord_unit_smul_zpow|placeOf|infinity`
- `namespace RationalFunctionField|heightOneSpectrumOfIrreducible|deg_placeOfPoint`
- `eq_of_le|eq_or_eq_top|overring|isUnit_iff|natDegree.*factor|sum.*natDegree|natDegree.*sum|multiplicity`
- `p06_9e0f5043ff_rmp_finite_place_model|p06_9e0f5043ff_rmp_finite_place_classification|p06_9e0f5043ff_rmp_infinity_place`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Polynomial/UniqueFactorization.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/FieldTheory/RatFunc/AsPolynomial.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1/decomposition-typecheck/Submission.frozen-source-check.log`

The DAG identifies the supplied statement as the depth-2 rational_model_principal child; the frozen root remains unchanged. DivisorClassGroup supplies Place, its DVR instance, normalized-order formulas, residue-field degree, degree_single, and HasPrincipalDivisors.exists_divisor. Mathlib supplies polynomial unique factorization and the proper-overring theorem ValuationSubring.eq_of_le_of_ne_top. Searches for the named RationalFunctionField constructions found only attribute references in specification files, not reusable construction definitions. Proposed names have no active-DAG or searched-source collisions. Both snapshot revisions and all nine dependencies match their manifests and have clean tracked files. Relevant project sources match the cached interface byte-for-byte. All three proposed types elaborate without warnings against the isolated import-only Submission interface. Definitional checks verify the canonical K-algebra through Polynomial.C and the residue-field algebra underlying Place.deg. Audited supporting declarations use only propext, Classical.choice, and Quot.sound. However, a fresh check of actual Submission.lean fails on three pre-existing unknown attribute targets: AlgebraicCurve.IsCurveOver.instNontrivialKaehler, AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply, and AlgebraicCurve.SemilinearAut.coe_torsion_smul. Actual import Submission validation remains an activation blocker; no comparator acceptance is claimed.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/748

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
