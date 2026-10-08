# Parent-supplied natural-language proof

- Parent DAG node: `root.level_one_valence_inequality-a1.indentation_limit-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.indentation_limit-a1.moving_interval_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Work along the filter of positive real ε tending to zero. On the eventual set in the hypothesis, F(ε,·) is interval-integrable between α(ε) and β(ε). The constant c is interval-integrable on every finite interval, so Hε(t) = F(ε,t)−c is interval-integrable there as well. The uniform bound at t = 0 also implies δ(ε) ≥ 0 on this eventual set.
2. Let E(ε) be the signed interval integral of Hε from α(ε) to β(ε). If α(ε) ≤ β(ε), the norm of this integral is at most the integral of |Hε|, hence at most δ(ε)(β(ε)−α(ε)). If β(ε) < α(ε), reverse the endpoints: the integral changes sign and its norm is unchanged, giving the bound δ(ε)(α(ε)−β(ε)). Thus in both cases |E(ε)| ≤ δ(ε)|β(ε)−α(ε)|. Equal endpoints give zero and obey the same estimate. This is also exactly intervalIntegral.norm_integral_le_of_norm_le_const in the pinned library.
3. Endpoint convergence gives β(ε)−α(ε) → b−a. Consequently |β(ε)−α(ε)| is eventually at most C = |b−a|+1. Intersect this eventual set with that of step 1. Because δ(ε) ≥ 0 there, step 2 gives 0 ≤ |E(ε)| ≤ Cδ(ε). The right-hand side tends to zero by δ(ε) → 0, so the squeeze theorem gives |E(ε)| → 0, and hence E(ε) → 0 in ℂ. Values outside these eventual sets do not affect the limits.
4. On the same eventual set, linearity of the signed interval integral yields ∫ from α(ε) to β(ε) F(ε,t) dt = E(ε) + c(β(ε)−α(ε)). Indeed the integral of the constant c is (β(ε)−α(ε)) times c, also when the endpoints are reversed; real scalar multiplication in ℂ equals multiplication by the real-to-complex cast.
5. The map x ↦ c(x:ℂ) is continuous, so c(β(ε)−α(ε)) → c(b−a). Add this to the limit E(ε) → 0 and use the eventual equality in step 4. The resulting limit is the required signed integral convergence.

## Key steps

1. Subtract the constant and obtain eventual interval integrability and nonnegative error bounds.
2. Bound the signed error integral by δ(ε)|β(ε)−α(ε)| in either endpoint order.
3. Use endpoint convergence to bound interval lengths and squeeze the error integral to zero.
4. Evaluate the integral of the constant with the signed endpoint difference.
5. Add the error limit to the continuous limit of the constant contribution.

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
