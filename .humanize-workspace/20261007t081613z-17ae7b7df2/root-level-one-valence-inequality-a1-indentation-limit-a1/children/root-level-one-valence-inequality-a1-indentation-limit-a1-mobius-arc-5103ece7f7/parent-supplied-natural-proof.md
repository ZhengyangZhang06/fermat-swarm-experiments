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
