# Parent-supplied natural-language proof

- Parent DAG node: `root.level_one_valence_inequality-a1.cusp_log_derivative-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.cusp_log_derivative-a1.qexp_finite_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Y₀ witnessing the expansion identity. The half-plane H={z:Im z>0} is open and convex, hence connected. The holomorphy hypothesis makes F analytic at every point of H, by DifferentiableOn.analyticOnNhd.
2. Let E consist of the points of H where F vanishes on a neighborhood. It is relatively open. If v∈H lies outside E, analyticOrderAt_eq_top shows that F has finite order at v. AnalyticAt.analyticOrderAt_ne_top in the pinned Mathlib/Analysis/Analytic/Order.lean gives F(u)=(u−v)^n b(u) on a neighborhood of v, with b analytic at v and b(v)≠0. Shrink to an open disk contained in H on which the factorization holds and b is nowhere zero, using continuity of b. In this disk F has no zero except possibly v. No point w of this disk can belong to E: intersecting a zero neighborhood of w with the disk would give a nonempty open set containing a point u≠v, contradicting the factorization. Thus H\E is relatively open, so E is relatively closed. The assumed nonzero value of F lies outside E. Connectedness gives E=∅.
3. Suppose analyticOrderAt A 0=⊤. By analyticOrderAt_eq_top, A vanishes on a neighborhood of zero. Choose δ>0 such that A(q)=0 whenever ‖q‖<δ.
4. Choose T strictly larger than 0, Y₀, and −log(δ)/(2π). Put q(z)=exp(2πiz). The complex exponential norm formula gives ‖q(z)‖=exp(−2π Im z). If Im z>T, positivity of π and exp(log δ)=δ imply ‖q(z)‖<δ. Also z∈H and Y₀≤Im z. Consequently F(z)=A(q(z))=0.
5. The set {z:Im z>T} is open and contains v=(T+1)i. Hence F vanishes on a neighborhood of this point of H, placing v in E. This contradicts step 2. Therefore analyticOrderAt A 0≠⊤.

## Key steps

1. Obtain analyticity of F throughout the connected open half-plane.
2. Use local finite-order factorization to show the zero-germ locus is relatively clopen, then exclude it using a nonzero value.
3. Infinite order of A would make A vanish on a disk about zero.
4. The exponential parameter maps a sufficiently high open half-plane into that disk.
5. The expansion identity would give a zero germ of F, contradicting the empty zero-germ locus.

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
