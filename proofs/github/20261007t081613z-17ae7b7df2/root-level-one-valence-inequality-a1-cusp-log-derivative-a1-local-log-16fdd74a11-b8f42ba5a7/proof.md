# Parent-supplied natural-language proof

- Parent DAG node: `root.level_one_valence_inequality-a1.cusp_log_derivative-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.cusp_log_derivative-a1.local_logderiv_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Set m=analyticOrderNatAt A 0. By AnalyticAt.analyticOrderAt_ne_top in the pinned Mathlib/Analysis/Analytic/Order.lean, there is B analytic at zero with B(0)≠0 and A(q)=q^m B(q) on a neighborhood of zero. Here scalar multiplication over ℂ is ordinary multiplication.
2. Analyticity supplies a neighborhood on which B is holomorphic. By continuity at zero, shrink it until ‖B(q)−B(0)‖<‖B(0)‖/2. The triangle inequality then gives ‖B(q)‖>‖B(0)‖/2>0. Intersect this neighborhood with the factorization neighborhood. Choose ρ>0 whose open disk lies in this intersection, and set r=ρ/2. Thus r>0, the factorization holds on the disk of radius 2r, and B is holomorphic and nowhere zero there. The product q^m B(q) is holomorphic there, so equality with A proves the required DifferentiableOn property on the disk of radius r.
3. Define G(q)=B′(q)/B(q). The derivative of a holomorphic function is holomorphic on its open domain, as supplied by DifferentiableOn.deriv in the pinned Mathlib/Analysis/Complex/CauchyIntegral.lean. Division by the nowhere-zero B shows that G is holomorphic, hence continuous, on the disk of radius 2r. The closed disk of radius r is nonempty, compact, and contained in that open disk. Therefore the continuous function q↦‖G(q)‖ attains a finite maximum there. Let M be the maximum of that value and zero. Then M≥0 and ‖G(q)‖≤M whenever ‖q‖≤r.
4. Fix q≠0 with ‖q‖<r. Factorization gives A(q)=q^m B(q)≠0. It holds on a neighborhood of q, so A has the same derivative there as this product. If m=0, the product is B and qA′(q)/A(q)−m=qG(q). If m>0, the product rule gives A′(q)=m q^(m−1)B(q)+q^m B′(q). Dividing by the nonzero q^m B(q), multiplying by q, and using q·q^(m−1)=q^m again gives qA′(q)/A(q)−m=qG(q). In these identities m denotes its cast to ℂ.
5. Taking norms yields ‖qA′(q)/A(q)−m‖=‖q‖‖G(q)‖≤‖q‖M=M‖q‖. Together with steps 2–4, this proves every stated conclusion.

## Key steps

1. Factor A(q)=q^m B(q) with B analytic and B(0) nonzero.
2. Choose a disk on which the factorization holds and B is holomorphic and nowhere zero.
3. Bound B′/B on a smaller compact closed disk.
4. Differentiate the local product, treating m=0 explicitly, to obtain qA′/A−m=qB′/B.
5. Use multiplicativity of the complex norm to obtain the linear bound.

## Reference use

### local-project

Queries:
- `analyticOrderAt_ne_top|analyticOrderNatAt_eq_iff|analyticOrderAt_eq_top|eqOn_zero_of_preconnected_of_eventuallyEq_zero`
- `norm_qParam|hasDerivAt_qParam|tendsto_qParam|def qParam`
- `analyticOrder|logDeriv|log_deriv`
- `sed -n '60,132p' Mathlib/Analysis/Analytic/Order.lean`
- `sed -n '195,232p' Mathlib/Analysis/Analytic/Uniqueness.lean`
- `sed -n '1,140p' Mathlib/Analysis/Calculus/LogDeriv.lean`
- `sed -n '135,265p' Mathlib/Analysis/Calculus/LogDeriv.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Theorems`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Uniqueness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Calculus/LogDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/Periodic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`

The snapshot pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The project search found no analytic-order or logarithmic-derivative matches in Definitions, P2M, or Theorems. Mathlib supplies finite-order factorization, the identity principle, logarithmic-derivative rules, holomorphy of derivatives, and the exponential parameter norm formula. The five inspected mathlib source files match the installed sources byte-for-byte; all nine installed dependencies are clean at their pinned revisions. Transitive axiom probes for the cited library declarations returned only propext, Classical.choice, and Quot.sound.
