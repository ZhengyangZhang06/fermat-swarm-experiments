<!-- theorem-id: fermat-p10/root.level_one_valence_inequality-a1.indentation_limit-a1.mobius_arc_estimates-a1 -->

## Theorem `Submission.p10_17ae7b7d_indent_mobius_arc_estimates`

Let v ∈ ℂ have Im v > 0, and let ε ∈ ℝ satisfy 0 < ε < 1. Define c = v−conj(v), w(t) = ε exp(it), and γ(t) = (v−conj(v)w(t))/(1−w(t)) for real t. Then γ and its real-parameter derivative γ′ are continuous. For every t, γ(t) ≠ v, γ(t)−v = cw(t)/(1−w(t)), γ has derivative ciw(t)/(1−w(t))² at t, and γ′(t)/(γ(t)−v) = i/(1−w(t)). Moreover |γ(t)−v| ≤ |c|ε/(1−ε), |γ′(t)| ≤ |c|ε/(1−ε)², and |γ′(t)/(γ(t)−v)−i| ≤ ε/(1−ε).

Node: `root.level_one_valence_inequality-a1.indentation_limit-a1.mobius_arc_estimates-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/424

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_indent_mobius_arc_estimates`

```lean
∀ (v : ℂ) (ε : ℝ), 0 < v.im → 0 < ε → ε < 1 → let w : ℝ → ℂ := fun t => (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I); let γ : ℝ → ℂ := fun t => (v - star v * w t) / (1 - w t); Continuous γ ∧ Continuous (deriv γ) ∧ ∀ t : ℝ, γ t ≠ v ∧ γ t - v = (v - star v) * w t / (1 - w t) ∧ HasDerivAt γ ((v - star v) * Complex.I * w t / (1 - w t) ^ 2) t ∧ deriv γ t / (γ t - v) = Complex.I / (1 - w t) ∧ ‖γ t - v‖ ≤ ‖v - star v‖ * ε / (1 - ε) ∧ ‖deriv γ t‖ ≤ ‖v - star v‖ * ε / (1 - ε) ^ 2 ∧ ‖deriv γ t / (γ t - v) - Complex.I‖ ≤ ε / (1 - ε)
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

- Parent DAG node: `root.level_one_valence_inequality-a1.indentation_limit-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.indentation_limit-a1.mobius_arc_estimates-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put c = v−conj(v). Its imaginary part is 2 Im v > 0, so c ≠ 0. For every real t, |exp(it)| = 1, hence |w(t)| = ε > 0 and w(t) ≠ 0. The reverse triangle inequality gives |1−w(t)| ≥ 1−|w(t)| = 1−ε > 0. Thus every denominator below is nonzero.
2. Subtract v in the definition of γ and put the terms over the common denominator: γ(t)−v = (v−conj(v)w(t)−v(1−w(t)))/(1−w(t)) = cw(t)/(1−w(t)). Since its three factors c, w(t), and (1−w(t))⁻¹ are nonzero, γ(t) ≠ v. Taking norms and using the denominator bound gives |γ(t)−v| = |c|ε/|1−w(t)| ≤ |c|ε/(1−ε).
3. Differentiation with respect to the real variable t gives w′(t) = iw(t): the real derivative of t ↦ exp(it) is i exp(it), and ε is constant. Using γ(t) = v + cw(t)/(1−w(t)), the quotient rule gives γ′(t) = c[(iw(t))(1−w(t))−w(t)(−iw(t))]/(1−w(t))² = ciw(t)/(1−w(t))². This establishes the stated HasDerivAt assertion at every real t, and therefore the same formula for deriv γ.
4. The function w is continuous. The defining expression for γ and the derivative formula are quotients and products of continuous functions with denominators nonzero at every real t. Therefore γ and deriv γ are both continuous on ℝ.
5. Divide the derivative formula by the nonzero expression in step 2 and cancel c and w(t). This gives γ′(t)/(γ(t)−v) = i/(1−w(t)). Taking norms in the derivative formula and using |i| = 1 gives |γ′(t)| = |c|ε/|1−w(t)|² ≤ |c|ε/(1−ε)².
6. Subtract i from the ratio in step 5: γ′(t)/(γ(t)−v)−i = iw(t)/(1−w(t)). Its norm is ε/|1−w(t)| ≤ ε/(1−ε). All estimates are independent of t, and steps 2–6 prove every asserted identity, continuity statement, and bound.

## Key steps

1. Use Im v > 0 to obtain c ≠ 0, and |w| = ε < 1 to bound the denominator away from zero.
2. Compute γ−v, show nonvanishing, and bound the distance to v.
3. Differentiate w and γ with respect to the real parameter.
4. Deduce continuity of the curve and its derivative from the explicit formulas.
5. Cancel nonzero factors in the normalized derivative and bound both the velocity and its normalized error from i.

## Reference use

### local-project

Queries:
- `indentation|pseudohyperbolic|analyticOrderAt_ne_top|logDeriv`
- `analyticOrderAt_ne_top|analyticOrderNatAt|norm_integral_le_of_norm_le_const|norm_integral_le|tendsto.*intervalIntegral`
- `AnalyticAt.deriv|AnalyticOnNhd.deriv|hasDerivAt_circleMap|deriv_circleMap|continuous_circleMap`
- `logDeriv.*(bounded|remainder)|remainder.*logDeriv|Tendsto.*intervalIntegral|tendsto_integral.*uniform`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Calculus/LogDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/indentation-decomposition-qpzicz2t/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/indentation-decomposition-qpzicz2t/TypesAfterSubmission.log`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The project-side search found no relevant match. The inspected mathlib files supply finite-order factorization, analytic derivative regularity, logarithmic-derivative product/power rules, real-parameter circle differentiation, and an orientation-independent interval-integral norm bound. Targeted searches found no exact bounded-remainder or moving-interval lemma in the searched files. All six inspected mathlib sources match the installed pinned library, and all nine dependencies are clean and revision-correct. The three proposed types elaborate after literal import Submission, with complex differentiation of f and real differentiation of γ confirmed explicitly. Type and cited-library axiom probes contain only propext, Classical.choice, and Quot.sound. The diagnostic report binds the checked Submission to its exact Git commit and records the approved policy digest, omissions of lines 10–12, reversible hashes, and fresh Lean confirmation that all 56 omitted targets are absent. These are diagnostic checks, not theorem acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/549

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
