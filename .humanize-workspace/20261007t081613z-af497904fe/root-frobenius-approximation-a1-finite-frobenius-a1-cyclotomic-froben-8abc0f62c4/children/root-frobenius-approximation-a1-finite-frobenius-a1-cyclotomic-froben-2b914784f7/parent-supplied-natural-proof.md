# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.mellin_tail_holomorphic-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix R, α, M and the stated hypotheses. Let μ be Lebesgue measure restricted to (1,∞). For t > 1 and s ∈ ℂ put f_s(t) = R(t)(t : ℂ)^(−(s+1)). Since t is positive, this complex power is exp(−(s+1)log t), with the real logarithm embedded in ℂ. Thus f_s is μ-measurable and, for σ = Re(s), its norm is |R(t)|t^(−σ−1) ≤ Mt^(α−σ−1). Complex-valued Borel measurable functions are strongly measurable here.
2. If σ > α, put δ = σ − α > 0. The dominating function Mt^(−1−δ) is integrable on (1,∞): substituting u = log t gives integral M∫_0^∞ exp(−δu)du = M/δ. Norm domination therefore proves Bochner integrability of f_s. Define I(s) by the stated Lebesgue integral; on this half-plane it is an absolutely convergent integral.
3. Fix s₀ with σ₀ = Re(s₀) > α, and put η = (σ₀ − α)/2 > 0. For |s−s₀| < η we have Re(s) > α + η. For each t > 1, s ↦ f_s(t) is entire, with derivative g_s(t) = −(log t)f_s(t). Throughout this disk the bounds |f_s(t)| ≤ Mt^(−1−η) and |g_s(t)| ≤ M(log t)t^(−1−η) hold. Both bounding functions are integrable. Indeed, u = log t transforms their integrals into M∫_0^∞ exp(−ηu)du = M/η and M∫_0^∞ u exp(−ηu)du = M/η². The latter evaluation follows by integration by parts, with antiderivative −(u/η + 1/η²)exp(−ηu); both terms tend to zero at infinity. For example, exp(ηu) ≥ (ηu)²/2 implies u exp(−ηu) → 0.
4. For a nonzero complex h with |h| < η, the segment s₀+vh, 0 ≤ v ≤ 1, stays in that disk. The ordinary fundamental theorem of calculus along this segment gives (f_{s₀+h}(t)−f_{s₀}(t))/h = ∫_0^1 g_{s₀+vh}(t)dv. Consequently every such difference quotient has norm at most M(log t)t^(−1−η). It is μ-measurable and converges pointwise, as complex h tends to zero, to g_{s₀}(t). Dominated convergence, applied to any sequence of nonzero complex increments tending to zero, gives convergence of the integrals of these quotients to ∫ g_{s₀} dμ. Since ℂ is a metric space, this sequential conclusion is the full limit as h → 0.
5. By step 2 both f_{s₀+h} and f_{s₀} are integrable. Linearity of their integrals identifies the integrated quotient in step 4 with (I(s₀+h)−I(s₀))/h. Hence I has complex derivative ∫ g_{s₀} dμ at s₀. The point s₀ was arbitrary in the open half-plane, so I is DifferentiableOn ℂ there. Together with step 2 this proves both asserted conclusions.

## Key steps

1. Rewrite the positive-real complex power as an exponential and obtain measurable kernels with norm bound Mt^(α−Re(s)−1).
2. Integrate the power bound to prove absolute Bochner integrability for Re(s) > α.
3. Choose a disk strictly inside the half-plane and uniformly dominate kernels and parameter derivatives by integrable power-log functions.
4. Bound complex difference quotients by integrating the derivative along each segment.
5. Apply dominated convergence and integral linearity to obtain the complex derivative at every point of the half-plane.

## Reference use

### local-project

Queries:
- `summable|integral|sumCoeff|cpow|nonneg`
- `differentiable.*[Mm]ellin|[Mm]ellin.*differentiable|hasDerivAt_integral|hasDerivAt.*[Mm]ellin`
- `measurable.*(floor|nat_floor)|measurable_to_countable`
- `integrableOn_Ioi_cpow_of_lt|integral_Ioi_cpow_of_lt|norm_ofReal_cpow`
- `def term|def LSeries|term_zero|term_def`
- `counting_mellin|mellin_tail|floor_remainder`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/LSeries/SumCoeff.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/LSeries/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/MellinTransform.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions`

The manifest pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. SumCoeff supplies LSeriesSummable_of_sum_norm_bigO_and_nonneg and LSeries_eq_mul_integral_of_nonneg; at exponent 1 these discharge the parent’s convergence and Abel-representation steps. Basic confirms that LSeries.term at n = 0 is zero. Floor supplies Nat.measurable_floor. ImproperIntegrals supplies integrableOn_Ioi_cpow_of_lt and integral_Ioi_cpow_of_lt for the main term. ParametricIntegral supplies differentiation under an integrable local derivative bound, also used in MellinTransform. The search for counting_mellin, mellin_tail, and floor_remainder found no matching declaration in project/Definitions, NumberTheory/LSeries, or Analysis/MellinTransform.lean. The local interfaces and cited library support passed the pinned compiler and transitive-axiom checks; only propext, Classical.choice, and Quot.sound occur.
