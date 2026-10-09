<!-- theorem-id: fermat-p10/root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1.rotation_coefficient_support-a1 -->

## Theorem `Submission.p10_17ae7b7d_rd_coeff_support`

Let w be a positive natural number, P : ℂ → ℂ, and p : FormalMultilinearSeries ℂ ℂ ℂ. Suppose HasFPowerSeriesAt P p 0, meaning that p is a convergent power-series expansion of P at zero. Write a_n = p.coeff n = p_n(1,…,1). Put ζ = exp(2πi/w). If there exists a real s > 0 such that P(ζt) = P(t) whenever ‖t‖ < s, then a_n = 0 for every natural n not divisible by w.

Node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1.rotation_coefficient_support-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/431

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_rd_coeff_support`

```lean
∀ (w : ℕ) (P : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ), 0 < w → HasFPowerSeriesAt P p 0 → (∃ s : ℝ, 0 < s ∧ ∀ t : ℂ, ‖t‖ < s → P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (w : ℂ)) * t) = P t) → ∀ n : ℕ, ¬ w ∣ n → p.coeff n = 0
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
- Child DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1.rotation_coefficient_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix w, P, p and the stated hypotheses. Choose s > 0 witnessing rotation invariance, and set ζ = exp(2πi/w). Since w > 0, its complex cast is nonzero and the exponent has real part zero. Thus ‖ζ‖ = 1. For every natural n, the exponential power identity gives ζ^n = exp(2πi n/w). The criterion Complex.exp_two_pi_mul_I_mul_div_eq_one_iff therefore gives ζ^n = 1 if and only if w divides n.
2. Set a_n = p.coeff n. One-dimensional multilinearity gives p_n(t,…,t) = t^n a_n, and ‖p_n‖ = ‖a_n‖. The hypothesis HasFPowerSeriesAt P p 0 supplies a positive convergence ball on which its sum is P. Choose a positive finite real R smaller than both that ball's radius and s. Consequently, P(t) = ∑_{n≥0} a_n t^n for ‖t‖ < R, and ∑_{n≥0} ‖a_n‖ρ^n converges for every real ρ with 0 < ρ < R.
3. Define d_n = a_n(ζ^n − 1). Since ‖ζ^n‖ = 1, the triangle inequality gives ‖d_n‖ ≤ 2‖a_n‖. Therefore ∑ ‖d_n‖ρ^n converges whenever 0 < ρ < R. For ‖t‖ < R, also ‖ζt‖ < R. Subtracting the two absolutely convergent expansions, using (ζt)^n = ζ^n t^n and rotation invariance, gives ∑_{n≥0} d_n t^n = P(ζt) − P(t) = 0.
4. Suppose some d_n is nonzero, and choose the least such index k. Fix ρ with 0 < ρ < R, and let S = ∑_{n>k} ‖d_n‖ρ^n. This is a finite nonnegative real number by step 3. For any complex t with 0 < ‖t‖ < ρ, all terms below k vanish. Dividing the absolutely convergent zero sum by the nonzero number t^k gives 0 = d_k + ∑_{n>k} d_n t^(n−k). The divided tail is absolutely convergent, since it is obtained by multiplying a subseries of an absolutely convergent series by the fixed scalar (t^k)⁻¹.
5. For n > k, one has n−k ≥ 1 and ‖t‖^(n−k) ≤ ‖t‖ρ^(n−k−1). Hence the tail estimate gives ‖d_k‖ ≤ ∑_{n>k} ‖d_n‖‖t‖^(n−k) ≤ ‖t‖ρ^(−k−1)S. Apply this to the positive real numbers t_m = ρ/(m+2), regarded as complex numbers. Each satisfies 0 < ‖t_m‖ < ρ, and their norms tend to zero. The right-hand side therefore tends to zero, forcing ‖d_k‖ = 0 and thus d_k = 0. This contradicts the choice of k. Consequently d_n = 0 for every n.
6. Let n be a natural number with w not dividing n. By step 1, ζ^n − 1 is nonzero. Step 5 gives a_n(ζ^n − 1) = 0, so cancellation in ℂ yields a_n = 0. Since a_n = p.coeff n, this is the required conclusion.

## Key steps

1. Show that ζ has norm one and ζ^n = 1 exactly when w divides n.
2. Express the given multilinear expansion as a scalar power series on a disk inside the invariance disk.
3. Subtract the rotated and original expansions to obtain a locally zero series with coefficients d_n = a_n(ζ^n − 1).
4. Assume a least nonzero coefficient and divide by the corresponding power of a nonzero input.
5. Bound the remaining tail by ‖t‖ρ^(−k−1)S and let positive real inputs tend to zero.
6. Cancel ζ^n − 1 when w does not divide n.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/600

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
