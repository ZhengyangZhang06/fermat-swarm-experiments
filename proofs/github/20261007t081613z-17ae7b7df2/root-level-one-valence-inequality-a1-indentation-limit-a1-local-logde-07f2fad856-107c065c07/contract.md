<!-- theorem-id: fermat-p10/root.level_one_valence_inequality-a1.indentation_limit-a1.local_logderiv_remainder-a1 -->

## Theorem `Submission.p10_17ae7b7d_indent_logderiv_remainder`

For every f : ℂ → ℂ and v : ℂ, if f is analytic at v and analyticOrderAt f v is finite, put m = analyticOrderNatAt f v. There exist r > 0, M ≥ 0, and G : ℂ → ℂ analytic on a neighborhood of every point of the closed disk |z−v| ≤ r, such that |G(z)| ≤ M on that closed disk and, whenever |z−v| < r and z ≠ v, f(z) ≠ 0 and f′(z)/f(z) = m/(z−v) + G(z). Here f′ is the complex derivative.

Node: `root.level_one_valence_inequality-a1.indentation_limit-a1.local_logderiv_remainder-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/424

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_indent_logderiv_remainder`

```lean
∀ (f : ℂ → ℂ) (v : ℂ), AnalyticAt ℂ f v → analyticOrderAt f v ≠ ⊤ → ∃ (r M : ℝ) (G : ℂ → ℂ), 0 < r ∧ 0 ≤ M ∧ AnalyticOnNhd ℂ G (Metric.closedBall v r) ∧ (∀ z ∈ Metric.closedBall v r, ‖G z‖ ≤ M) ∧ ∀ z ∈ Metric.ball v r, z ≠ v → f z ≠ 0 ∧ deriv f z / f z = (analyticOrderNatAt f v : ℂ) / (z - v) + G z
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
- Child DAG node: `root.level_one_valence_inequality-a1.indentation_limit-a1.local_logderiv_remainder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let m = analyticOrderNatAt f v. By AnalyticAt.analyticOrderAt_ne_top in the pinned Mathlib/Analysis/Analytic/Order.lean, the hypotheses give B : ℂ → ℂ analytic at v, with B(v) ≠ 0, such that f(z) = (z−v)^m B(z) throughout some neighborhood of v. Scalar multiplication in that factorization is ordinary complex multiplication.
2. Analyticity at v supplies an open neighborhood on which B is analytic at every point. Continuity of B at v and B(v) ≠ 0 supply a neighborhood on which B never vanishes. Intersect these neighborhoods with an open neighborhood where the factorization holds. Choose ρ > 0 with the open disk of radius ρ centered at v inside this intersection, and set r = ρ/2. Then r > 0 and its closed disk lies inside the open disk of radius ρ.
3. Define G(z) = B′(z)/B(z), using the complex derivative. At each point of the open disk of radius ρ, B′ is analytic by AnalyticAt.deriv, and division by the nonzero analytic function B preserves analyticity. Thus G is analytic on a neighborhood of every point of the closed disk of radius r, hence continuous there. Compactness of this closed disk and continuity of the norm give a real upper bound K for |G|. Taking M = max(0,K) gives M ≥ 0 and |G(z)| ≤ M on the entire closed disk.
4. Fix z with |z−v| < r and z ≠ v. Both z−v and B(z) are nonzero, so the factorization implies f(z) ≠ 0. Since the factorization holds on an open neighborhood of z, its two sides have equal complex derivatives at z.
5. If m = 0, the local factorization is f = B, so f′(z)/f(z) = G(z) = m/(z−v)+G(z). If m ≥ 1, product and power differentiation give f′(z) = m(z−v)^(m−1)B(z) + (z−v)^m B′(z). Dividing by the nonzero value (z−v)^m B(z) and cancelling yields f′(z)/f(z) = m/(z−v) + B′(z)/B(z). This is the required identity, completing all conclusions for r, M, and G.

## Key steps

1. Factor the finite-order analytic germ as (z−v)^m times a nonvanishing analytic factor.
2. Choose a smaller closed disk inside the common open neighborhood of factorization, analyticity, and nonvanishing.
3. Define G = B′/B and bound its norm on the compact closed disk.
4. Use local equality to differentiate the factorization away from v and divide by its nonzero value, including the m = 0 case.

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

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
