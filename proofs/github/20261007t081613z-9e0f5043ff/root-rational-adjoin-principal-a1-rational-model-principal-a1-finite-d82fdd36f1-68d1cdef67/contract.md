<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.residue_degree-a1.residue_evaluation_surjective-a1 -->

## Theorem `Submission.p06_9e0f5043ff_fpm_rd_residue_surjective`

Let K and F be fields, with a K-algebra structure on F. Let x ∈ F be transcendental over K, let q ∈ K[T] be irreducible, and let v : AlgebraicCurve.Place K F. Put A = v.toValuationSubring and let ρ : A → κ(v) be the canonical residue homomorphism. Assume every h ∈ A has an expression, in F, h = a(x)/b(x) with a,b ∈ K[T] and q not dividing b. Let e : K[T] → A be a K-algebra homomorphism whose composite with A → F is evaluation at x. If ρ(e(q)) = 0, then the ring homomorphism ρ ∘ e : K[T] → κ(v) is surjective.

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.residue_degree-a1.residue_evaluation_surjective-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/110

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_fpm_rd_residue_surjective`

```lean
∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F), Transcendental K x → ∀ q : Polynomial K, Irreducible q → ∀ v : AlgebraicCurve.Place K F, (∀ h : v.toValuationSubring, ∃ a b : Polynomial K, ¬ q ∣ b ∧ (h : F) = Polynomial.aeval x a / Polynomial.aeval x b) → ∀ e : Polynomial K →ₐ[K] v.toValuationSubring, (∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a) → IsLocalRing.residue v.toValuationSubring (e q) = 0 → Function.Surjective ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom)
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

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.residue_degree-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.residue_degree-a1.residue_evaluation_surjective-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write R = K[T], A = v.toValuationSubring, E(a) = a(x), and φ = ρ ∘ e. Let r be any element of κ(v). The residue map is the quotient map by the maximal ideal and is surjective, so choose h ∈ A with ρ(h) = r.
2. By the representation hypothesis, choose a,b ∈ R with q not dividing b and with the image of h in F equal to E(a)/E(b). Since q divides zero, b ≠ 0. Evaluation at the transcendental element x is injective: an equality of evaluations gives a polynomial relation for their difference, which must be the zero polynomial. Hence E(b) ≠ 0.
3. There exist u,t ∈ R with u q + t b = 1. To justify this, let d be a greatest common divisor of q and b. It divides both. If d were a nonunit, write q = d c. Irreducibility of q would force c to be a unit, so q would be associated to d. Since d divides b, this would imply q divides b, a contradiction. Thus d is a unit. The Euclidean algorithm supplies u₀,t₀ with u₀ q + t₀ b = d. Multiplication by the inverse of d in R gives the asserted u and t.
4. Apply φ to the Bezout identity. The hypothesis φ(q) = 0 and the homomorphism identities give φ(t)φ(b) = 1. Commutativity also gives φ(b)φ(t) = 1.
5. In F, the fraction identity from step 2 and E(b) ≠ 0 imply h E(b) = E(a), where h denotes its image in F. The compatibility of e with evaluation identifies this as the image of h e(b) = e(a). The inclusion A → F is injective, so that equality holds in A. Applying ρ gives r φ(b) = φ(a).
6. Multiply the equality in step 5 by φ(t). By step 4 and associativity, r = (r φ(b))φ(t) = φ(a)φ(t) = φ(a t). Therefore a t is a preimage of r under φ. Since r was arbitrary, φ is surjective.

## Key steps

1. Lift an arbitrary residue-field element to the valuation ring.
2. Represent the lift by a permitted fraction and establish a nonzero evaluated denominator.
3. Use irreducibility and the Euclidean algorithm to obtain a Bezout inverse for the denominator modulo q.
4. Apply the residue evaluation map and the vanishing of q to obtain an inverse residue.
5. Clear the denominator inside the valuation ring and pass to residues.
6. Exhibit the polynomial a t as a preimage of the prescribed residue.

## Reference use

### local-project

Queries:
- `rg -n 'def deg|def ResidueField|abbrev ResidueField|residue.*[Hh]om|namespace Place' project/Definitions/Def_AlgebraicCurve*.lean`
- `rg -n 'finrank.*natDegree|natDegree.*finrank|powerBasis|quotientKerEquivOfSurjective|quotientKerAlgEquiv' mathlib/Mathlib/RingTheory/AdjoinRoot.lean mathlib/Mathlib/RingTheory/Polynomial/Quotient.lean mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean mathlib/Mathlib/LinearAlgebra/Isomorphisms.lean`
- `rg -n 'injective.*aeval|aeval.*injective|IsCoprime.*dvd|[Ii]sCoprime.*[Ii]rreducible' mathlib/Mathlib/RingTheory/Algebraic/Basic.lean mathlib/Mathlib/RingTheory/Coprime mathlib/Mathlib/RingTheory/Bezout.lean`
- `rg -n 'irreducible.*[Cc]oprime|Irreducible.*[Cc]oprime|[Cc]oprime.*irreducible|[Cc]oprime.*Irreducible' mathlib/Mathlib -g '*.lean'`
- `rg -n 'residue.*(natDegree|aeval)|natDegree.*[Rr]esidue|fpm.*(kernel|surject)' project/Definitions project/Submission.lean`
- `rg -n 'p06_9e0f5043ff_fpm_rd_eval_kernel|p06_9e0f5043ff_fpm_rd_residue_surjective' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes -g '*.json' -g '!**/local-references/**'`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/PrincipalIdealDomain.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/AdjoinRoot.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/README.txt`
- `/tmp/p06-residue-degree-decomposition-9e0f5043ff/CheckTypes.lean`
- `/tmp/p06-residue-degree-decomposition-9e0f5043ff/CheckTypes.log`

Snapshot-relative queries were run from the specified snapshot. The manifest pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Place.deg is the canonical residue-field finrank. Existing results supply transcendental_iff_injective, residue_surjective, residue_ne_zero_iff_isUnit, Irreducible.coprime_iff_not_dvd, Ideal.quotientKerAlgEquivOfSurjective, and finrank_quotient_span_eq_natDegree. The targeted project search found no matching polynomial-local residue result; both proposed names were absent from the inspected DAG and node metadata. All dependency revisions matched their manifest and were clean; cached Definitions sources matched the snapshot byte-for-byte. Both proposed types elaborated with Lean 4.33.1 after import Submission in the existing isolated import-only interface cache. Definitional-equality checks confirmed that the canonical K-algebra residue map has exactly the ring homomorphism used below. The inspected library declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. Validation limitation: this cache uses an import-only Submission interface because the original frozen source has pre-existing unknown attribute targets. These checks are interface validation, not exact-contract comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/261

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
