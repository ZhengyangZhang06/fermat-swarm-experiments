# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N≠0. If N=1, Γ₀(1)=SL₂(ℤ), so Q is a singleton. The only divisor of 1 is the squarefree divisor 1, giving the required sum 1. Assume N>1 and put R=ℤ/Nℤ and H=Γ₀(N).
2. Let P_N be the set of unimodular rows (r,s) over R, modulo common multiplication by a unit. Here unimodular means that xr+ys=1 for some x,y∈R. Unit scaling preserves this property, and identity, inverse and product of units establish an equivalence relation. Thus P_N is a quotient of a subset of the finite set R² and is finite.
3. Send a right coset Hα to the class of the bottom row of α modulo N. If α has top row (a,b) and bottom row (c,d), its determinant equation gives (−b)c+ad=1, so this row is unimodular. If η∈H, its reduction has bottom row (0,e); its determinant equation makes e a unit. The bottom row of ηα is therefore e times that of α. This proves well-definedness.
4. If α and β have bottom rows (r,s) and (r′,s′) with (r′,s′)=u(r,s), then the bottom-left entry of βα⁻¹ reduces to r′s−s′r=0. Hence βα⁻¹∈H and Hβ=Hα, proving injectivity. For every unimodular residue row, the sibling theorem p10_17ae7b7d_cc_lift_unimodular_row applies with this nonzero N and supplies α with precisely that bottom row. This proves surjectivity. Finally Hα↦α⁻¹H is a well-defined bijection from right cosets to Q, with inverse αH↦Hα⁻¹. Consequently Q is finite and |Q|=|P_N|.
5. For a prime p and a≥1, a residue modulo pᵃ is a unit precisely when its integer representative is not divisible by p. A unit cannot reduce to zero modulo p. Conversely, a representative not divisible by p is coprime to pᵃ, and a Bézout identity supplies its inverse. A row over ℤ/pᵃℤ is unimodular exactly when at least one coordinate is a unit: one unit gives the required linear combination, while two coordinates divisible by p cannot generate 1 after reduction modulo p.
6. Thus each local row class has a unique representative either [1:t], with arbitrary t modulo pᵃ, or [s:1], with s divisible by p. Normalize the first coordinate if it is a unit; otherwise normalize the second. Multiplication by a unit preserves divisibility by p, so the charts are disjoint. Within either chart the coordinate 1 forces the scaling unit to equal 1, proving uniqueness. The chart sizes are pᵃ and p^{a−1}: the latter residues are exactly p times the representatives 0,…,p^{a−1}−1. Hence |P_{pᵃ}|=pᵃ+p^{a−1}.
7. Write N=∏ᵢpᵢ^{aᵢ}, with distinct primes and positive exponents. Existence of prime factorization follows by induction, factoring a composite into smaller positive integers. For uniqueness, Bézout implies Euclid's lemma: if p∤a and p∣ab, multiply a Bézout identity for p,a by b to get p∣b. Successive cancellation yields unique prime exponents and, in particular, this decomposition into pairwise coprime prime powers.
8. Chinese remaindering identifies R with ∏ᵢℤ/pᵢ^{aᵢ}ℤ as a ring. For two coprime moduli a,b, if ua+vb=1 then Avb+Bua realizes prescribed residues A,B. If a∣n and b∣n, writing n=at and multiplying ua+vb=1 by t proves b∣t, hence ab∣n; this proves uniqueness modulo ab. Induction gives the finite-product bijection, and reduction preserves ring operations.
9. Under this ring isomorphism, unimodular rows and unit scalings are componentwise. A global linear-combination witness or inverse projects to each component; conversely the component witnesses or inverses assemble through the isomorphism. Choosing row representatives in each component therefore gives a bijection P_N≃∏ᵢP_{pᵢ^{aᵢ}}: if component rows differ by units, their tuple is a single unit of the product ring. It follows that |P_N|=∏ᵢ(pᵢ^{aᵢ}+pᵢ^{aᵢ−1}).
10. Expand this finite product. Choosing pᵢ^{aᵢ−1} precisely for a subset J of the primes and pᵢ^{aᵢ} elsewhere contributes N/d, where d=∏_{i∈J}pᵢ. Unique prime factorization identifies these subsets bijectively with the squarefree positive divisors of N. Therefore the product equals ∑_{d∣N, d squarefree}N/d, which is the defining value of ModularCurve.dedekindPsi N. Together with step 4 this proves both conclusions.

## Key steps

1. Identify right cosets with unit classes of unimodular residue rows, using the lifting sibling for surjectivity.
2. Use inversion to obtain finiteness and the same cardinality for left cosets.
3. Count the two unique prime-power charts.
4. Apply Chinese remaindering to row classes.
5. Expand the product as the sum over squarefree divisors.

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
