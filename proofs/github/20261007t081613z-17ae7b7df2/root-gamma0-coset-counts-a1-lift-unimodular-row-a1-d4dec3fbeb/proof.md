# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.lift_unimodular_row-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N≠0 and r,s with xr+ys=1 in R=ℤ/Nℤ. If N=1, R has one element, so the identity matrix has the required reductions. Hence assume N>1.
2. Choose an integer D representing s with 1≤D≤N: use the representative in {1,…,N−1} if s≠0, and use N if s=0. Let P be the finite set of primes dividing D but not N. The moduli consisting of N and the distinct primes in P are positive and pairwise coprime.
3. Choose an integer C congruent to r modulo N and to 1 modulo every p in P. To justify this simultaneous choice, for coprime positive a,b the Euclidean algorithm gives integers u,v with ua+vb=1; given representatives A modulo a and B modulo b, Avb+Bua has both prescribed residues. A product of moduli already used is coprime to the next one: multiplying Bézout identities proves that coprimality with each factor implies coprimality with their product. Induction therefore constructs C for the stated finite family.
4. No prime divides both C and D. Indeed, if p divides D and not N, its defining congruence gives C≡1 modulo p. If p divides D and N, a hypothetical p∣C would make both r and s zero after reduction from ℤ/Nℤ to ℤ/pℤ. Reducing xr+ys=1 would give 0=1 in ℤ/pℤ, impossible for a prime p.
5. Consequently gcd(|C|,D)=1. This gcd is positive since D>0; if it exceeded 1, its least divisor greater than 1 would be prime and divide both C and D, contradicting step 4.
6. The integer Euclidean algorithm now gives a,b∈ℤ with aC+bD=1. Set A=((b,−a),(C,D)). Its determinant is bD+aC=1, so A belongs to SL₂(ℤ). Its bottom row reduces to (r,s) by construction, proving the exact assertion.

## Key steps

1. Handle N=1 using the identity matrix.
2. Choose a positive representative D of the second coordinate.
3. Use Bézout and finite Chinese remaindering to choose C avoiding the primes of D outside N.
4. Use unimodularity to exclude common prime factors inside N.
5. Apply integer Bézout to C,D and construct the determinant-one matrix.

## Reference use

### local-project

Queries:
- `surject|lift|coprime|Coprime`
- `SpecialLinearGroup.*surject|surject.*SpecialLinearGroup|[Gg]amma0.*card|[Gg]amma0.*index|[Pp]rojectiveLine.*[Cc]ard|[Cc]ard.*[Pp]rojectiveLine|[Tt]ransvection.*surject`
- `p10_17ae7b7d_cc_(lift_unimodular_row|index|elliptic_fixed_points|translation_orbits)`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o TargetAbsence.olean TargetAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o ChildTypes.olean ChildTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ProjectiveLineMatrixAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Totient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p10-coset-split-nairohng/TargetAbsence.lean`
- `/tmp/p10-coset-split-nairohng/ChildTypes.lean`
- `/tmp/p10-coset-split-nairohng/ChildTypes.log`
- `/tmp/p10-coset-split-nairohng/report.json`

The snapshot matches project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; both tracked snapshot trees and all nine pinned dependency checkouts were clean. Existing infrastructure supplies same-ring Bézout row completion, Chinese remaindering, totient formulas, Gamma0 finiteness, and quotient actions. Searches found no matching integer lift of a unimodular residue row or the requested counting formulas, and no reservation of the proposed names in local DAGs. The separate projective-line modules are not in the frozen imports. All four literal types compiled after import Submission in /tmp/p10-coset-split-nairohng; reflexivity probes checked left coset multiplication, subgroup restriction and matrix multiplication. The types and selected imported lemmas reported only propext, Classical.choice and Quot.sound. Policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 matched; only listed lines 10–12 were omitted in the disposable copy, and Lean verified all 56 targets absent. The report records exact omitted lines, reversible reconstruction, original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and build hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539. Original contract and Submission were unchanged. These are interface diagnostics, not comparator acceptance of proofs.
