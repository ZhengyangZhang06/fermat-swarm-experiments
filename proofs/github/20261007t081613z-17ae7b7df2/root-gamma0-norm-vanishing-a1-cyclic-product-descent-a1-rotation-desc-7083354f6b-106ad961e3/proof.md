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
