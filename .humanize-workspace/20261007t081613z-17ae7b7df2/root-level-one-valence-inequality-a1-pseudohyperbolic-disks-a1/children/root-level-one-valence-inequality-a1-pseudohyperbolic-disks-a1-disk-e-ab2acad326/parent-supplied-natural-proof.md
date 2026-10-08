# Parent-supplied natural-language proof

- Parent DAG node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_euclidean_description-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write v=x+iy, with x,y real and y>0. Put Δ=1−ε²=(1−ε)(1+ε), Y=y(1+ε²)/Δ, C=x+iY, and R=2yε/Δ. Since 0<ε<1, both factors defining Δ are positive, so Δ>0 and R>0.
2. Let z=u+it with t>0. The imaginary part of z−conj(v) is t+y>0, so this denominator is nonzero and its norm is positive. Multiplicativity of the complex norm gives ‖(z−v)/(z−conj(v))‖=‖z−v‖/‖z−conj(v)‖. Multiplying by the positive denominator and then squaring the nonnegative sides shows that the ratio inequality is equivalent to (u−x)²+(t−y)²≤ε²((u−x)²+(t+y)²).
3. For all real u,t, direct expansion gives the identity Δ((u−x)²+(t−Y)²−R²)=(u−x)²+(t−y)²−ε²((u−x)²+(t+y)²). Indeed, ΔY=y(1+ε²) and Δ(Y²−R²)=y²Δ, the latter following from (1+ε²)²−4ε²=(1−ε²)². Because Δ>0, the inequality in step 2 is equivalent to (u−x)²+(t−Y)²≤R².
4. The expression on the left is ‖z−C‖². Since both ‖z−C‖ and R are nonnegative, this squared inequality is equivalent to ‖z−C‖≤R, namely membership in Metric.closedBall C R. Thus for every z with Im(z)>0, membership in D(v,ε) is equivalent to membership in that closed ball.
5. Every point of this closed ball has positive imaginary part. In fact, Y−R=y(1+ε²−2ε)/Δ=y(1−ε)/(1+ε)>0. If z=u+it lies in the ball, then |t−Y|≤‖z−C‖≤R, hence t≥Y−R>0.
6. For a point in D(v,ε), step 4 proves membership in the closed ball. Conversely, for a point in the closed ball, step 5 supplies the half-plane condition and step 4 supplies the ratio inequality. The two sets are therefore equal, with precisely the center and radius asserted.

## Key steps

1. Prove positivity of 1−ε² and the proposed radius.
2. For points in the upper half-plane, clear the nonzero denominator and square the norm inequality.
3. Use the explicit completed-square identity.
4. Interpret the resulting inequality as Euclidean closed-ball membership.
5. Show the whole Euclidean ball has imaginary part at least y(1−ε)/(1+ε)>0.
6. Combine both membership implications to obtain equality of sets.

## Reference use

### local-project

Queries:
- `genusFormula|weight_two|finrank.*CuspForm|CuspForm.*finrank|Riemann.?Roch`
- `pseudohyperbolic|pseudo_hyperbolic|pseudoHyperbolic`
- `denom_ne_zero|im_smul|normSq|im_div|norm_conj|star_def|closedBall|moebius|mobius`
- `rg -n --hidden --no-ignore -g dag.json -g '!**/.lake/**' -g '!**/local-references/**' 'p10_17ae7b7d_phdisk_(euclidean|mobius_image)' /mnt/data/zhengyang-workspace/fermat-swarm-projects`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Complex/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/Norm.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root/natural-proof-v140.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root/natural-audit-v140.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1-pseudohyperbolic-disks-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/pseudohyperbolic-split-sha5f2su/report.json`

The snapshots match project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d and are clean; all nine installed dependencies also match their pins and are clean. No pseudohyperbolic terminology match was found. The inspected files provide the exact genus numerics, complex conjugation and norm identities, Möbius denominator nonvanishing and imaginary-part formulas, and a related hyperbolic-ball Euclidean description. The four inspected complex-analysis source files match the installed library byte-for-byte; selected transitive axiom checks report only propext, Classical.choice, and Quot.sound. Neither proposed name occurs in searched DAGs. Both proposed types, the conjugation/norm/metric probes, and their composition into the frozen geometric parent pass a complete Lean check after import Submission in a disposable copy of its exact proof base. The report records the approved policy digest, reversible omission of only lines 10–12, original/build hashes, and a successful Lean absence probe for all 56 omitted targets. These are decomposition diagnostics, not comparator acceptance.
