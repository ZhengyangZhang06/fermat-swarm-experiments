# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N≠0 and the stated lifting hypothesis. Write R=ℤ/Nℤ, G=SL₂(ℤ), and H=Γ₀(N). If xr+ys=1 and u is a unit, then (xu⁻¹)(ur)+(yu⁻¹)(us)=1. Thus unit scaling preserves unimodularity. The identity unit gives reflexivity, inversion gives symmetry, and multiplication of scaling units gives transitivity. Consequently the equivalence relation generated in the displayed Quot is precisely unit scaling. Since R has N elements, U is finite, and its quotient P is finite.
2. For A=[[a,b],[c,d]]∈G, the determinant equation ad−bc=1 reduces to (−b)c+ad=1 in R. Hence the reduced bottom row of A belongs to U. Associate to the right coset HA the class of this row.
3. If η∈H, its reduction has the form [[k,l],[0,e]]. Its determinant equation gives ke=1, so e is a unit with inverse k. The bottom row of ηA is e times the bottom row of A. Therefore the association is independent of the representative of HA.
4. Suppose A and B have reduced bottom rows (r,s) and (r′,s′), and their classes in P agree. By step 1 there is a unit u with r′=ur and s′=us. The bottom-left entry of BA⁻¹ reduces to r′s−s′r=urs−usr=0. Thus BA⁻¹∈H. Writing B=(BA⁻¹)A shows HB=HA. The map from right cosets to P is injective.
5. Given any class in P, choose a representative (r,s) and its unimodularity witnesses. The lifting hypothesis supplies A∈G whose reduced bottom row is exactly (r,s). Its right coset maps to that class, so the map is surjective.
6. Inversion gives a bijection from right cosets to left cosets by HA↦A⁻¹H. Indeed, replacing A by ηA with η∈H replaces A⁻¹ by A⁻¹η⁻¹, which represents the same left coset. Its inverse is AH↦HA⁻¹, well-defined because replacing A by Aη replaces A⁻¹ by η⁻¹A⁻¹. Composing this bijection with steps 2–5 gives a bijection Q≃P. Finiteness transfers from P to Q, and a bijection of finite types gives Nat.card Q=Nat.card P. The argument also applies to N=1, since it never assumes that R is nontrivial.

## Key steps

1. Verify that unit scaling is an equivalence relation on unimodular rows and that its quotient is finite.
2. Map a right coset to the reduced bottom-row class and prove representative independence.
3. Use the bottom-left entry of BA⁻¹ to prove injectivity.
4. Apply the explicit row-lifting hypothesis to prove surjectivity.
5. Invert cosets to transfer the bijection, finiteness, and cardinality equality to left cosets.

## Reference use

### local-project

Queries:
- `dedekindPsi|ProjectiveLine|unimodularRow|Gamma0`
- `card.*ProjectiveLine|ProjectiveLine.*card|Gamma0.*(index|card)|(index|card).*Gamma0|dedekindPsi`
- `chineseRemainder|primeFactors|factorization|isUnit_iff|isUnit.*coprime`
- `prod_pow_primeFactors|prod.*factorization|factorization.*prod|squarefree_iff|Squarefree.*factorization`
- `rg -n 'p10_17ae7b7d_idx_(coset_row_card|prime_power_row_card|crt_row_card|dedekind_psi_product)' .humanize --glob 'dag.json' --glob 'parent-child-handoff.json'`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o TargetAbsence.olean TargetAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o ChildTypes.olean ChildTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-coset-index-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Factorization/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Squarefree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/index-split-ssqaob6l/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/index-split-ssqaob6l/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/index-split-ssqaob6l/report.json`

The snapshot matches project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Both tracked snapshot trees and all nine pinned dependency checkouts were clean. The sources supply the squarefree-divisor definition of dedekindPsi, Chinese remaindering, the prime-power unit criterion, prime factorization, and the left-coset convention. No matching coset-index or projective-row cardinality theorem was found. The projective-line module is outside the frozen imports, so the proposed types express its mathematical quotient explicitly using Quot. No proposed name occurred in local DAGs or frozen handoffs. All four exact types compiled after import Submission; reflexivity checks confirmed the left-coset quotient, scalar unit multiplication, and special-linear matrix multiplication. The types and checked library declarations have only propext, Classical.choice and Quot.sound as transitive axioms. The matching policy digest was 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96. Only listed lines 10–12 were omitted in the disposable compiler copy; Lean confirmed all 56 targets absent. The receipt records exact omitted text, reversible reconstruction, original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and build hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539. Original contracts and handoffs were unchanged. These are interface diagnostics, not comparator acceptance of theorem proofs.
