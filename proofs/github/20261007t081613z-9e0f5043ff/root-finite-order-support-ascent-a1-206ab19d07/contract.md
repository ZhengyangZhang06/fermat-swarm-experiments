<!-- theorem-id: fermat-p06/root.finite_order_support_ascent-a1 -->

## Theorem `Submission.p06_9e0f5043ff_finite_order_support_ascent`

Let K, E and L be fields with compatible K-algebra structures on E and L and an E-algebra structure on L, forming a scalar tower K → E → L. Suppose L/E is finite-dimensional and separable. Assume that for every nonzero a in E, the set of project places v of E over K with ord_v(a) ≠ 0 is finite. Then for every nonzero f in L, the set of project places w of L over K with ord_w(f) ≠ 0 is finite.

Node: `root.finite_order_support_ascent-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/100, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/101

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_finite_order_support_ascent`

```lean
∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FiniteDimensional E L] [Algebra.IsSeparable E L], (∀ a : E, a ≠ 0 → {v : AlgebraicCurve.Place K E | v.ord a ≠ 0}.Finite) → ∀ f : L, f ≠ 0 → {w : AlgebraicCurve.Place K L | w.ord f ≠ 0}.Finite
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
- Child DAG node: `root.finite_order_support_ascent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the fields, compatible scalar tower and finite separable extension in the statement, and assume the stated finite-support hypothesis on E. Fix f ≠ 0 in L. Finite-dimensionality implies that f and f⁻¹ are algebraic over E: sufficiently many powers are linearly dependent, and dividing a nontrivial dependence by its highest nonzero coefficient gives a monic polynomial. Choose monic polynomials P,Q over E annihilating f and f⁻¹, respectively.

2. Let C be the finite set of nonzero coefficients occurring in P or Q. It is finite because a polynomial has finitely many nonzero coefficients. For each a in C, let S_a be the set of project places v of E over K where ord_v(a) ≠ 0. Every S_a is finite by hypothesis. Hence T = ⋃a∈C S_a is finite.

3. At a project place v, a nonzero element a with nonnegative order lies in its valuation ring. Indeed, choose a uniformizer π and use Place.exists_unit_mul_zpow to write a = uπ^(ord_v(a)); a nonnegative exponent is a natural power of an element of the ring. In particular order zero implies membership. Zero belongs to the ring separately. Therefore, if v is outside T, every coefficient of P and Q belongs to O_v: each nonzero coefficient has order zero there, and zero coefficients require no condition.

4. Every project place w of L over K restricts to a project place v = w.restrict E. This is the existing algebraic restriction construction in Def_AlgebraicCurve_DivisorPushPull.lean; its algebraicity hypothesis follows from finite-dimensionality. Its defining valuation subring is the inverse image of O_w under E → L. Consequently the image of O_v is contained in O_w. The scalar-tower hypothesis ensures that this restriction still contains the given image of K.

5. Suppose v = w.restrict E lies outside T. Map P and Q to polynomials over L. By steps 3–4 all their coefficients belong to O_w, and they remain monic. Their roots are f and f⁻¹. Apply the existing Place.mem_of_eval_monic_eq_zero from Def_AlgebraicCurve_PlacesOverDVR.lean to obtain f ∈ O_w and f⁻¹ ∈ O_w. Equivalently, one may see the integral-root assertion directly: a root z of negative order in a monic equation would, after division by the leading power of z, put 1 in the maximal ideal, since each lower term has positive order. Thus neither of these two roots can have negative order.

6. Since f and f⁻¹ both belong to O_w, f is a unit of O_w, with inverse f⁻¹. The project order of a unit is zero, by Place.ord_coe_unit. Therefore ord_w(f) = 0 whenever w.restrict E is outside T.

7. For each v in T, the fiber {w | w.restrict E = v} is finite by Place.finite_setOf_restrict_eq in Def_AlgebraicCurve_PlacesOverDVR.lean. Its hypotheses are precisely a compatible field tower, finite-dimensionality and separability; it does not assume principal divisors or finite order support upstairs.

8. Step 6 gives {w | ord_w(f) ≠ 0} ⊆ ⋃v∈T {w | w.restrict E = v}. The right side is a finite union of finite sets by steps 2 and 7, and hence is finite. Its subset on the left is finite. Since f was arbitrary and nonzero, this proves the exact assertion.

## Key steps

1. Choose monic equations over E for f and f⁻¹.
2. Take the finite union of the downstairs order supports of their nonzero coefficients.
3. Outside that union, place all coefficients in the restricted valuation ring and then in the upstairs ring.
4. Apply integral closedness to put both f and f⁻¹ in the upstairs ring.
5. Conclude that f has order zero outside the fibers over the exceptional set.
6. Use the existing finite-fiber theorem to prove finite support upstairs.

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

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
