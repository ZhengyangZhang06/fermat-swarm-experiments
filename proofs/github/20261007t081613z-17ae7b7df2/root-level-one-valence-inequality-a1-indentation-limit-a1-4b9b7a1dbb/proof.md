# Parent-supplied natural-language proof

- Parent DAG node: `root.level_one_valence_inequality-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.indentation_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put m=analyticOrderNatAt f v. Analyticity and finite order give a local factorization f(z)=(z−v)^m B(z), with B analytic near v and B(v)≠0, by AnalyticAt.analyticOrderAt_ne_top. Choose r>0 so that the factorization holds on a neighborhood of the closed disk |z−v|≤r and B is holomorphic and nonvanishing there. The holomorphic function G=B′/B is bounded in norm by some M≥0 on this closed disk. On its punctured interior, differentiating the factorization gives f′(z)/f(z)=m/(z−v)+G(z). This also holds for m=0.
2. Set c=v−conj(v), which is nonzero because Im v>0, and w(ε,t)=ε exp(it). For 0<ε<1, one has |w|=ε, w≠0, and |1−w|≥1−ε>0. Algebra in the definition of γ gives γ(ε,t)−v=cw/(1−w). Thus γ(ε,t)≠v and |γ(ε,t)−v|≤|c|ε/(1−ε), uniformly in all real t. For every sufficiently small positive ε, the entire parametrized circle lies in |z−v|<r, and f is nonzero along it by the factorization.
3. Differentiating with respect to the real variable t gives ∂tγ=ciw/(1−w)². Consequently (∂tγ)/(γ−v)=i/(1−w)=i+iw/(1−w), and |∂tγ|≤|c|ε/(1−ε)².
4. Substitute these formulas into the logarithmic-derivative identity from step 1. For all sufficiently small positive ε and all t, the integrand equals im+imw/(1−w)+G(γ(ε,t))∂tγ(ε,t). Its difference from the constant im therefore has norm at most δ(ε)=mε/(1−ε)+M|c|ε/(1−ε)². This bound is independent of t and tends to zero as ε→0 from above.
5. For each such ε the integrand is continuous in t: the curve is smooth, the sampled values remain in the analytic neighborhood, and the denominators are nonzero. Hence it is integrable on the compact interval between α(ε) and β(ε). The integral of the constant im over the signed interval is im(β(ε)−α(ε)). Applying the interval-integral norm estimate to the error gives a norm bound δ(ε)|β(ε)−α(ε)|. The estimate holds in either endpoint order, by reversing the interval if necessary.
6. The endpoint hypotheses imply β(ε)−α(ε)→b−a and make |β(ε)−α(ε)| eventually bounded. Since δ(ε)→0, the error integral tends to zero. Meanwhile im(β(ε)−α(ε)) tends to im(b−a). Adding these limits proves the claimed convergence with the stated casts and orientation.

## Key steps

1. Factor the analytic germ and separate its logarithmic derivative into a pole and a bounded holomorphic remainder.
2. Express γ−v as (v−conj(v))w/(1−w) and obtain uniform shrinking and nonvanishing.
3. Compute the real-parameter derivative of γ.
4. Bound the integrand's difference from the constant i times the order uniformly in t.
5. Integrate the error over the signed interval and bound it by the endpoint distance.
6. Use convergence of the endpoints and vanishing of the uniform error.

## Reference use

### local-project

Queries:
- `\bvalence\b|argument.?principle|windingnumber`
- `analyticOrderNatAt_eq_iff|analyticOrderAt_ne_top|analyticOrderAt_eq_top`
- `eqOn_zero|eqOn_of|finite|eq_zero_or|frequently`
- `logDeriv_mul|logDeriv_comp|logDeriv_pow`
- `integral_eq_sub_of_hasDerivAt_of_le|norm_integral_le_of_norm_le_const`
- `sed -n '1,150p' project/Definitions/Def_ModularCurve_GenusNumerics.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Calculus/LogDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Searches of mathlib/Mathlib/Analysis/Complex and project/Definitions found no valence, argument-principle, or winding-number implementation. The inspected library supplies local analyticity, the identity principle, finite-order factorization, logarithmic-derivative rules, local primitives, and interval-integral estimates. The cited library declarations passed transitive axiom probes using only propext, Classical.choice, and Quot.sound. All nine installed dependencies matched their pinned revisions and were Git-clean.
