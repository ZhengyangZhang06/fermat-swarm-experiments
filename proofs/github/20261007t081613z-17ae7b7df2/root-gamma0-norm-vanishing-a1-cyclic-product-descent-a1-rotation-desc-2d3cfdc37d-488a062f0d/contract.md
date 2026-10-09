<!-- theorem-id: fermat-p10/root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1.sparse_series_descent-a1 -->

## Theorem `Submission.p10_17ae7b7d_rd_sparse_series_descent`

Let w be a positive natural number, P : ℂ → ℂ, and p : FormalMultilinearSeries ℂ ℂ ℂ. Suppose HasFPowerSeriesAt P p 0, meaning that p is a convergent power-series expansion of P at zero. Assume p.coeff n = 0 for every natural n not divisible by w. Then there exist C : ℂ → ℂ analytic at zero and a real r > 0 such that P(t) = C(t^w) whenever ‖t‖ < r.

Node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1.sparse_series_descent-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/431

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_rd_sparse_series_descent`

```lean
∀ (w : ℕ) (P : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ), 0 < w → HasFPowerSeriesAt P p 0 → (∀ n : ℕ, ¬ w ∣ n → p.coeff n = 0) → ∃ C : ℂ → ℂ, AnalyticAt ℂ C 0 ∧ ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r → P t = C (t ^ w)
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

- Parent DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1`
- Child DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1.sparse_series_descent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix w, P, p and the stated hypotheses, and write a_n = p.coeff n. One-dimensional multilinearity gives p_n(t,…,t) = t^n a_n and ‖p_n‖ = ‖a_n‖. Choose a positive finite real R strictly smaller than a convergence-ball radius supplied by HasFPowerSeriesAt P p 0. Then P(t) = ∑_{n≥0} a_n t^n for ‖t‖ < R, and ∑_{n≥0} ‖a_n‖ρ^n converges for every 0 < ρ < R.
2. Choose r with 0 < r < R, set q = r^w, and define b_ℓ = a_(wℓ). Then q > 0. Since w > 0, the map ℓ ↦ wℓ is injective. The nonnegative summable series ∑_{n≥0} ‖a_n‖r^n therefore has a summable subseries indexed by wℓ. Using (r^w)^ℓ = r^(wℓ), this says that ∑_{ℓ≥0} ‖b_ℓ‖q^ℓ converges.
3. If ‖u‖ < q, then for each ℓ, ‖b_ℓ u^ℓ‖ = ‖b_ℓ‖‖u‖^ℓ ≤ ‖b_ℓ‖q^ℓ. Comparison with step 2 proves absolute convergence of ∑ b_ℓ u^ℓ. More explicitly, form the scalar formal multilinear series B = FormalMultilinearSeries.ofScalars ℂ b. Its ℓth operator norm equals ‖b_ℓ‖. The summability established in step 2 and the convergence-radius bound from summability imply that B.radius is at least q, viewed as a nonnegative extended real number. In particular, B.radius is positive.
4. Define C(u) = ∑_{ℓ≥0} b_ℓ u^ℓ when ‖u‖ < q, and C(u) = 0 otherwise. Because ℂ is complete and B.radius > 0, the sum of B has B as a convergent power-series expansion at zero and is analytic there. Scalar-series evaluation identifies this sum with ∑ b_ℓ u^ℓ wherever ‖u‖ < q. Thus C agrees with that analytic sum on the open disk of radius q around zero. Analyticity at a point is preserved by agreement on a neighborhood, so C is analytic at zero.
5. Let t satisfy ‖t‖ < r. Since w > 0 and 0 ≤ ‖t‖ < r, strict monotonicity of the positive integer power gives ‖t^w‖ = ‖t‖^w < r^w = q. Hence C(t^w) is given by its series. The series ∑ a_n t^n is absolutely convergent by step 1. If n is outside the image of ℓ ↦ wℓ, then w does not divide n, so the support hypothesis gives a_n = 0. Removing these zero terms and reindexing along the injective map ℓ ↦ wℓ therefore gives P(t) = ∑_{ℓ≥0} a_(wℓ)t^(wℓ).
6. For each ℓ, the natural-power identity t^(wℓ) = (t^w)^ℓ converts the last sum into ∑_{ℓ≥0} b_ℓ(t^w)^ℓ = C(t^w). This calculation also holds at t = 0: w > 0 ensures that only ℓ = 0 contributes, and both sides equal a_0. The function C from step 4 and the positive radius r from step 2 satisfy precisely the required conclusion.

## Key steps

1. Convert the given one-variable multilinear expansion into scalar coefficients with absolute convergence on a positive disk.
2. Extract the coefficients indexed by wℓ and prove weighted summability at q = r^w using injectivity.
3. Construct their scalar formal power series and bound its convergence radius below by q > 0.
4. Define C by the compressed series near zero and prove its analyticity by local agreement with the series sum.
5. Use the support hypothesis to restrict and reindex the absolutely convergent expansion of P.
6. Apply t^(wℓ) = (t^w)^ℓ and verify the constant-term identity at zero.

## Reference use

### local-project

Queries:
- `exp_two_pi_mul_I_mul_div_eq_one_iff|ofScalars|HasFPowerSeriesAt|analytic.*pow|pow.*analytic`
- `rotation|ofScalars|HasFPowerSeriesAt|exp_two_pi_mul_I_mul_div_eq_one_iff`
- `ofScalars|coeff|hasFPowerSeriesAt_iff|summable|radius`
- `coeff|unique|eq_formal|hasFPowerSeriesAt`
- `coeff|le_radius_of_summable|summable_norm_mul_pow|hasFPowerSeries|analyticAt`
- `def coeff|norm_coeff|apply_eq_prod_smul_coeff|apply_eq_pow_smul_coeff`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/OfScalars.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Uniqueness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/ConvergenceRadius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The targeted project search returned no matches. FormalMultilinearSeries.lean provides scalar coefficients, diagonal evaluation, and equality of coefficient norm with multilinear operator norm. Basic.lean provides local scalar-sum characterizations and analyticity of convergent series sums. OfScalars.lean supplies scalar-series construction and its norm identity; ConvergenceRadius.lean supplies absolute convergence inside the radius and a radius bound from summability. Uniqueness.lean supplies one-variable coefficient uniqueness. Log.lean:160 supplies the exponential divisibility criterion. The six inspected mathlib files match the pinned build sources byte-for-byte; all nine dependency checkouts match their pins and are clean. The checked library declarations have only propext, Classical.choice, and Quot.sound as transitive axioms.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/525

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
