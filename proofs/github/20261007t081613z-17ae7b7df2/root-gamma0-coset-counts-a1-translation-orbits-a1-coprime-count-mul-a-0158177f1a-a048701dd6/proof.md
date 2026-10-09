# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1.translation_period-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N and q, and choose A∈SL₂(ℤ) with q=AΓ₀(N). Write A=((a,b),(c,d)); then ad−bc=1 and A⁻¹=((d,−b),(−c,a)).
2. Induction on the natural exponent k gives T^k=((1,k),(0,1)): the formula holds for k=0, and multiplication by T changes the upper-right entry from k to k+1 while preserving the other three entries. In particular T^N=((1,N),(0,1)).
3. The bottom-left entry of A⁻¹T^NA is (−c)(a+Nc)+ac=−Nc². It is divisible by N, so h=A⁻¹T^NA belongs to Γ₀(N).
4. The equality T^NA=Ah now gives T^N·q=T^NAΓ₀(N)=AhΓ₀(N)=AΓ₀(N)=q, as required.

## Key steps

1. Represent the coset by a determinant-one integer matrix.
2. Compute the powers of the translation matrix.
3. Show A⁻¹T^NA has bottom-left entry −Nc² and belongs to Γ₀(N).
4. Conclude that left multiplication by T^N fixes the coset.

## Reference use

### local-project

Queries:
- `ProjectiveLine|Unimodular|unimodular|cusp|orbit`
- `def chineseRemainder|theorem.*chineseRemainder|castHom|chineseRemainder.*apply`
- `def Gamma0|mem_Gamma0|Gamma0.*(map|inf|mul)|T_zpow|T_pow`
- `orbit.*[Cc]oprime|[Cc]oprime.*orbit|Gamma0.*[Cc][Rr][Tt]|Gamma0.*(equivProd|prodEquiv)|cuspCount.*mul`
- `p10_17ae7b7d_ccm_(coset_crt_equivariant|translation_period|coprime_orbit_product)`
- `python3 /tmp/p10_ccm_decomposition_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/SetTheory/Cardinal/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/Submission.original.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/ParentAssembly.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/report.json`
- `/runtime/operator-header-policy-v1/policy.json`

The clean snapshots matched project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine compiler dependencies matched their pins with clean tracked files. Relevant infrastructure includes ZMod.chineseRemainder, Gamma0_mem, left-coset actions, and Nat.card_prod without finiteness assumptions. The targeted search found no matching equivariant Gamma0 CRT theorem or coprime orbit-product theorem. The separate projective-line module is outside the frozen imports, so the proposed interfaces use existing cosets and group actions. The frozen proof base c77074cc2682d4bf219f2909b6b4767445f7f7bc already contains the accepted unimodular-row lifting theorem. All three exact child types elaborated after import Submission; matrix multiplication, left-coset action, diagonal product action, and subgroup restriction passed explicit instance probes. Their conditional composition proved the exact parent type. The proposed names were absent from the DAG, handoffs, and imported environment. Audited interfaces, the existing lifting theorem, and relevant library declarations use only propext, Classical.choice, and Quot.sound. Disposable compiler copies followed policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: only lines 10–12 were omitted, all 56 targets passed Lean absence checks, and reversible original/build hashes are recorded. Concurrent changes to the working Submission body triggered a housekeeping assertion; all compiler checks used the frozen copy, and the original contract and current Submission header were rechecked successfully. These are interface diagnostics, not comparator acceptance of the proposed proofs.
