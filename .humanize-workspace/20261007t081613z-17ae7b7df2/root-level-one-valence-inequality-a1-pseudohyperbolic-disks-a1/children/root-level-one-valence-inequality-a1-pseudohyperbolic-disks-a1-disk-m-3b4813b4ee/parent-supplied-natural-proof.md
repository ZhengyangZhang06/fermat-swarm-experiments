# Parent-supplied natural-language proof

- Parent DAG node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated v,ε,a,b,c,d, and put H={z∈ℂ : Im(z)>0}. For any z=u+it∈H, write Q(z)=cz+d. If c≠0, then Im(Q(z))=ct≠0, so Q(z)≠0. If c=0, the determinant equation gives ad=1, hence d≠0 and again Q(z)≠0.
2. Multiplication of numerator and denominator by conj(Q(z)) gives Im(M(z))=((at)(cu+d)−(au+b)ct)/|Q(z)|²=(ad−bc)t/|Q(z)|²=t/|Q(z)|²>0. Thus M maps H into H. The same calculation applies to every real coefficient quadruple of determinant one.
3. Define N(w)=(dw−b)/(−cw+a). Its coefficient determinant is da−(−b)(−c)=ad−bc=1, so steps 1–2 show that its denominator is nonzero on H and N maps H into H. For z∈H, direct fraction subtraction gives −cM(z)+a=1/Q(z) and dM(z)−b=z/Q(z). Consequently N(M(z))=z. Similarly, for w∈H put P(w)=−cw+a. Then cN(w)+d=1/P(w) and aN(w)+b=w/P(w), so M(N(w))=w. All cancellations are valid since Q(z) and P(w) are nonzero.
4. Let z,v∈H. Subtracting fractions and expanding their numerators, using ad−bc=1, gives M(z)−M(v)=(z−v)/(Q(z)Q(v)). Real coefficients imply conj(M(v))=(a conj(v)+b)/(c conj(v)+d), and c conj(v)+d=conj(Q(v))≠0. The same numerator calculation therefore gives M(z)−conj(M(v))=(z−conj(v))/(Q(z)conj(Q(v))). The imaginary part of z−conj(v) is Im(z)+Im(v)>0. By step 2, the imaginary part of M(z)−conj(M(v)) is also positive. Both differences used as denominators are thus nonzero.
5. Dividing the two identities from step 4 and cancelling the nonzero factors yields (M(z)−M(v))/(M(z)−conj(M(v)))=((z−v)/(z−conj(v)))·conj(Q(v))/Q(v). Conjugation preserves the norm, and Q(v)≠0, so ‖conj(Q(v))/Q(v)‖=‖Q(v)‖/‖Q(v)‖=1. Taking norms proves equality of the original and transformed ratio norms for all z,v∈H. This argument holds for every determinant-one real coefficient quadruple, so it also applies to N.
6. If w belongs to the image M(D(v,ε)), choose z∈D(v,ε) with M(z)=w. Then z∈H, step 2 gives w∈H, and step 5 gives the ratio bound at w with center M(v). Thus w∈D(M(v),ε), proving the forward inclusion.
7. Conversely, let w∈D(M(v),ε). Both w and M(v) lie in H. Step 3 gives N(w)∈H and N(M(v))=v. Apply step 5 to N and the pair w,M(v); the ratio bound for w becomes the defining ratio bound for N(w) with center v. Hence N(w)∈D(v,ε). Step 3 gives M(N(w))=w, so w is in M(D(v,ε)). This proves the reverse inclusion and the asserted image equality.

## Key steps

1. Prove Möbius denominators are nonzero on the upper half-plane.
2. Compute the imaginary part and prove half-plane preservation.
3. Construct the determinant-one inverse and verify both inverse identities.
4. Derive the two difference identities with all denominator nonvanishing conditions.
5. Cancel to obtain the transformed ratio and prove its extra factor has norm one.
6. Prove the forward image inclusion.
7. Use the inverse ratio identity to prove the reverse image inclusion.

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
