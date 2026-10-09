# Parent-supplied natural-language proof

- Parent DAG node: `root.level_one_valence_inequality-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.cusp_log_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. The open half-plane H is convex and connected. Holomorphy gives analyticity at each point by DifferentiableOn.analyticAt. Let E consist of points of H near which F vanishes identically. This set is relatively open. At a point outside E, the Taylor series has a first nonzero coefficient, so locally F(u)=(u−v)^n b(u), where b is analytic and b(v)≠0. After shrinking the disk, b is nowhere zero; hence this disk contains no point of E. Thus E is relatively closed as well. The assumed nonzero value makes E proper, so connectedness gives E=∅. In particular, F cannot vanish on any nonempty open subset of H.
2. Suppose analyticOrderAt A 0 were infinite. By analyticOrderAt_eq_top, A would vanish on a disk about zero. Put q(z)=exp(2πiz). The exponential is nonzero and ‖q(z)‖=exp(−2π Im z), which tends to zero as Im z tends to infinity. Consequently the expansion identity would make F vanish on an open upper half-plane above both Y₀ and a sufficiently large height. This contradicts step 1. Therefore analyticOrderAt A 0 is finite.
3. Put m=analyticOrderNatAt A 0. Finite-order factorization, as stated by AnalyticAt.analyticOrderAt_ne_top and AnalyticAt.analyticOrderNatAt_eq_iff in the pinned Order.lean, supplies an analytic B with B(0)≠0 and A(q)=q^m B(q) near zero. Choose r>0 so that this identity holds on |q|<2r and B is holomorphic and nowhere zero there. Such a choice follows by shrinking a neighborhood of analyticity and using continuity of B at zero.
4. The function G=B′/B is holomorphic on |q|<2r and continuous on the compact disk |q|≤r. Choose M≥0 bounding its norm there. Choose Y>0 with Y>Y₀ and exp(−2πY)<r. For every z with Im z≥Y, q(z) lies in this disk and F(z)=q(z)^m B(q(z))≠0.
5. At each such z, the expansion and factorization hold throughout a neighborhood of z: the inequalities Im z>Y₀ and |q(z)|<r are strict. Differentiating there, using q′=2πiq and q≠0, gives F′(z)/F(z)=2πi(m+q(z)G(q(z))). This identity also holds when m=0, since the derivative of q^0 is zero.
6. Set C=2πM, which is nonnegative. Subtracting 2πim from the identity in step 5 and taking norms gives ‖F′(z)/F(z)−2πim‖=2π‖q(z)‖‖G(q(z))‖≤C exp(−2π Im z). Together with steps 2 and 4, this proves every asserted conclusion.

## Key steps

1. Use connectedness and analytic local factorization to exclude a zero germ of F anywhere in H.
2. A zero germ of A would force F to vanish on an open upper half-plane.
3. Factor A(q)=q^m B(q) with B analytic and nonvanishing near zero.
4. Bound B′/B on a smaller closed disk and choose a sufficiently large positive height.
5. Differentiate the expansion and obtain the uniform exponential estimate.

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
