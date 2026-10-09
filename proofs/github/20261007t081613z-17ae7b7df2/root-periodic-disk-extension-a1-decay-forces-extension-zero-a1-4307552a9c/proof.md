# Parent-supplied natural-language proof

- Parent DAG node: `root.periodic_disk_extension-a1`
- Child DAG node: `root.periodic_disk_extension-a1.decay_forces_extension_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix w,g,A satisfying the hypotheses. For every nonzero q, let L=Complex.log q and z=wL/(2πi). Complex.exp_log gives exp(2πiz/w)=q. The exponential norm identity gives Im z=−w log‖q‖/(2π). These identities are also recorded as qParam_right_inv and im_invQParam in the pinned Mathlib/Analysis/Complex/Periodic.lean.
2. Fix ε>0 and choose its decay threshold Y. Put H₀=max(1,Y) and r=exp(−2πH₀/w), so 0<r<1. If 0<‖q‖<r, the point z from step 1 has Im z>H₀≥Y and Im z>0. The factorization and decay assumptions therefore give ‖A(q)‖=‖g(z)‖≤ε. Thus every positive ε bounds A on some punctured disk about zero.
3. Suppose for contradiction that A(0)≠0, and set a=‖A(0)‖>0 and ε=a/3. Choose r>0 from step 2 for this ε. By continuity at zero, there is δ>0 such that ‖A(q)−A(0)‖<ε whenever ‖q‖<δ. Choose the complex number q whose real part is min(r,δ)/2 and whose imaginary part is zero. It satisfies 0<‖q‖<r and ‖q‖<δ. Hence the triangle inequality gives a≤‖A(0)−A(q)‖+‖A(q)‖<ε+ε=2a/3, a contradiction.
4. Therefore A(0)=0. The argument concerns the given A throughout and makes no new choice of extension.

## Key steps

1. Construct exponential preimages and compute their heights.
2. Convert each decay threshold into a bound on a punctured disk.
3. Combine that bound with continuity at zero to contradict a nonzero value.
4. Conclude that the given extension vanishes at zero.

## Reference use

### local-project

Queries:
- `qParam|cuspFunction|analyticOrderAt|periodic_disk_extension|pde_holomorphic_extension|pde_finite_order|pde_decay_zero`
- `removable|differentiableOn|bounded|exists|limUnder`
- `analyticOrderAt_eq_top|eqOn_zero|eqOn_of_preconnected|exists_eventuallyEq_pow|analyticAt`
- `exp_log|exp_eq_exp_iff_exists_int`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/Periodic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/RemovableSingularity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`

The snapshot records project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Periodic.lean supplies the q-parameter norm, inverse, and descent API; its global-periodicity hypotheses must not be confused with the parent's periodicity restricted to the upper half-plane. RemovableSingularity.lean provides bounded removable singularities. CauchyIntegral.lean:625 supplies holomorphic-to-analytic conversion; IsolatedZeros.lean:185 supplies local factorization; Order.lean:86,101 identifies the two orders. Log.lean:41,171 supplies exponential surjectivity onto nonzero complex numbers and its integer-period fibers. FundThmCalculus.lean:1140 supports the segment argument. The search found no matching analytic-extension or analytic-order lemma in Def_ModularCurve_GenusNumerics.lean. Inspected mathematical sources match the installed pinned sources; all nine dependencies were clean and matched their pins. The checked library declarations depend only on propext, Classical.choice, and Quot.sound.
