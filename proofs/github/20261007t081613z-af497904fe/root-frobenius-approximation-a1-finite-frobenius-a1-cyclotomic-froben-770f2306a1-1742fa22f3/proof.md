# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.floor_remainder_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a, κ, α, C and the stated hypotheses. For n ∈ ℕ put A_n = Σ_{k=1}^n a(k), with A_0 = 0, and for t ∈ ℝ put R(t) = A_{Nat.floor(t)} − κt.
2. The map Nat.floor : ℝ → ℕ is measurable: the inverse image of {0} is (−∞,1), and for n ≥ 1 the inverse image of {n} is [n,n+1); these are Borel sets. Every subset of ℕ is a countable union of singletons, so all its inverse images are Borel. The map n ↦ A_n from the discrete measurable space ℕ to ℝ is measurable. Therefore t ↦ A_{Nat.floor(t)} is measurable. Subtracting the continuous function t ↦ κt proves measurability of R on all of ℝ.
3. Fix t ≥ 1 and put n = Nat.floor(t). The floor inequalities give n ≥ 1 and 0 ≤ t − (n : ℝ) < 1. In particular 1 ≤ (n : ℝ) ≤ t. The identity R(t) = (A_n − κ(n : ℝ)) + κ((n : ℝ) − t), the triangle inequality, and the counting hypothesis imply |R(t)| ≤ C(n : ℝ)^α + |κ|(t − (n : ℝ)) ≤ C(n : ℝ)^α + |κ|.
4. Because α ≥ 0 and 1 ≤ (n : ℝ) ≤ t, monotonicity of real powers on positive bases gives (n : ℝ)^α ≤ t^α and 1 ≤ t^α. Multiplying these inequalities by C ≥ 0 and |κ| ≥ 0 respectively yields |R(t)| ≤ Ct^α + |κ|t^α = (C + |κ|)t^α. This proves the claimed bound for every t ≥ 1 and completes both conclusions.

## Key steps

1. Prove natural-floor measurability from its Borel level sets and compose with the sequence of finite sums.
2. Subtract κt to obtain a globally measurable remainder.
3. Use n = Nat.floor(t) ≥ 1 and 0 ≤ t − n < 1 to compare the real remainder with the integer error.
4. Use α ≥ 0 to bound n^α and 1 by t^α.

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
