<!-- theorem-id: fermat-p10/root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1 -->

## Theorem `Submission.p10_17ae7b7d_cpd_rotation_descent`

Let w be a positive natural number and P:ℂ→ℂ be analytic at zero. Put ζ=exp(2πi/w). Suppose there exists a real s>0 such that P(ζt)=P(t) whenever ‖t‖<s. Then there exist C:ℂ→ℂ analytic at zero and a real r>0 such that P(t)=C(t^w) whenever ‖t‖<r.

Node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/403

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/457, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/458

## Lean problem

Declaration: `Submission.p10_17ae7b7d_cpd_rotation_descent`

```lean
∀ (w : ℕ) (P : ℂ → ℂ), 0 < w → AnalyticAt ℂ P 0 → (∃ s : ℝ, 0 < s ∧ ∀ t : ℂ, ‖t‖ < s → P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (w : ℂ)) * t) = P t) → ∃ C : ℂ → ℂ, AnalyticAt ℂ C 0 ∧ ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r → P t = C (t ^ w)
```

### Frozen project context

`Fermat/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean` at `a97febc53b1c4d489edc54ca44132af7a21279b3` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.CuspSpace.cuspDenomAux_infty
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one

set_option autoImplicit false

theorem CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero (N : ℕ) [NeZero N]
    (hg : ModularCurve.genusFormula N = 0) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f = 0 := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1`
- Child DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix w>0 and P analytic at zero, and take s>0 witnessing the stated local rotation invariance. Put ζ=exp(2πi/w). The exponent has real part zero, so ‖ζ‖=1. For every natural n, the exponential power identity gives ζ^n=exp(2πin/w). Since w≠0, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff gives ζ^n=1 if and only if w divides n.
2. Analyticity gives complex Taylor coefficients a_n and a positive real R<s such that P(t)=∑_{n≥0}a_n t^n for ‖t‖<R, with absolute convergence at every radius smaller than R. Since ‖ζ‖=1, substituting ζt is valid on this same disk. Local invariance implies ∑_{n≥0}d_n t^n=0 there, where d_n=a_n(ζ^n−1). These series are absolutely convergent; indeed ‖d_n‖≤2‖a_n‖.
3. All d_n vanish. For completeness, if some d_n were nonzero, let k be its least such index and choose 0<ρ<R. For 0<‖t‖<ρ, division of the zero series by t^k gives 0=d_k+∑_{n>k}d_n t^(n−k). Let S=∑_{n>k}‖d_n‖ρ^n, which is finite. The norm of the tail is at most ‖t‖ρ^(−k−1)S, since ‖t‖^(n−k)≤‖t‖ρ^(n−k−1) for n>k. As nonzero t tends to zero, this bound tends to zero, forcing d_k=0, a contradiction. Thus a_n(ζ^n−1)=0 for every n. If w does not divide n, step 1 makes the second factor nonzero, so a_n=0.
4. Choose 0<r<R and put q=r^w>0. Absolute convergence gives ∑_{n≥0}‖a_n‖r^n<∞. The map ℓ↦wℓ is injective because w>0; hence ∑_{ℓ≥0}‖a_(wℓ)‖q^ℓ=∑_{ℓ≥0}‖a_(wℓ)‖r^(wℓ) is a convergent subseries. For ‖u‖<q, the series ∑_{ℓ≥0}a_(wℓ)u^ℓ converges absolutely by comparison with this subseries. It is a power series with convergence radius at least q>0.
5. Define C(u) to be this sum for ‖u‖<q and zero outside that disk. The positive convergence radius means its sum is analytic at zero; C agrees with that sum on a neighborhood of zero, so C is analytic at zero as well.
6. If ‖t‖<r, positivity of w gives ‖t^w‖=‖t‖^w<r^w=q. By step 3 all terms of the Taylor series of P with indices outside the image of ℓ↦wℓ vanish. Absolute convergence permits restriction to that image and reindexing, giving P(t)=∑_{ℓ≥0}a_(wℓ)t^(wℓ)=∑_{ℓ≥0}a_(wℓ)(t^w)^ℓ=C(t^w). At t=0 the same identity holds by the constant terms, since w>0 and only ℓ=0 contributes. The function C and radius r satisfy exactly the required conclusion.

## Key steps

1. Establish ‖ζ‖=1 and ζ^n=1 exactly when w divides n.
2. Expand P and P(ζ·) in absolutely convergent Taylor series on a common disk.
3. Use coefficient uniqueness, with an explicit tail estimate, to eliminate all coefficients whose indices are not divisible by w.
4. Show the selected coefficients a_(wℓ) define a power series of positive convergence radius.
5. Define C locally by that series and extend it by zero outside the disk.
6. Reindex the absolutely convergent Taylor series to prove P(t)=C(t^w), including t=0.

## Reference use

### local-project

Queries:
- `analyticOrderNatAt.*(comp|mul|prod|pow)|analyticOrderAt.*(comp|mul|prod|pow)|exp_two_pi_mul_I_mul_div_eq_one_iff`
- `invariant|divisib|comp_pow|iterate.*coeff`
- `eq_formalMultilinearSeries|unique|coeff|eq_of`
- `hasFPowerSeries|analyticAt|summable.*radius|le_radius`
- `cyclic.*(product|prod|descent)|rotation.*(descent|invariant)|analytic.*(root.of.unity|comp_pow)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/OfScalars.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Uniqueness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/ConvergenceRadius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`

The clean snapshot matches project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Order.lean supplies local factorization, analyticOrderAt_congr, analyticOrderAt_pow, and AnalyticAt.analyticOrderAt_comp. Uniqueness.lean supplies uniqueness of one-variable analytic expansions. OfScalars.lean and ConvergenceRadius.lean support scalar series and convergence-radius bounds from summability. Log.lean:160 supplies the exponential divisibility criterion. Targeted searches found no matching analytic rotation-descent theorem. All nine dependency checkouts match their pins and are clean. The checked proposition definitions and cited library declarations depend only on propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
