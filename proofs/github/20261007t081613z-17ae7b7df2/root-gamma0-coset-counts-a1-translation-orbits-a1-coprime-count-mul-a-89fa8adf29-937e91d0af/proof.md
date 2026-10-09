# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1.coset_crt_equiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix nonzero coprime m,n and put K=mn. For any positive coprime integers A,B, choose u,v∈ℤ with uA+vB=1. Given integer representatives x,y, the integer xvB+yuA has residues x modulo A and y modulo B. If A and B both divide z, write z=At. Then t=uAt+vBt is divisible by B, so AB divides z. Consequently reduction is a bijection ℤ/(AB)ℤ→ℤ/Aℤ×ℤ/Bℤ. Since reduction preserves addition, multiplication, and 1, it is a ring isomorphism. This argument also covers A=1 or B=1.
2. An integer is divisible by K exactly when it is divisible by both m and n. Applying this to the bottom-left matrix entry gives H_K=H_m∩H_n. Define F:Q_K→Q_m×Q_n by F(AH_K)=(AH_m,AH_n). This is well-defined because H_K is contained in both subgroups. If F(AH_K)=F(BH_K), then A⁻¹B belongs to H_m and H_n, hence to H_K. Thus AH_K=BH_K, proving injectivity.
3. We establish the lifting fact needed for surjectivity, including its construction. Let L be any positive natural number and let r,s∈ℤ/Lℤ satisfy xr+ys=1 for some x,y. Choose a positive integer c representing r: use its least nonnegative representative when that representative is positive, and otherwise use c=L. Choose an integer s₀ representing s. Let D be the product of the distinct positive primes dividing c but not L, with empty product 1. Every prime dividing D fails to divide L, so gcd(L,D)=1. Choose U,V∈ℤ with UL+VD=1 and set d=s₀VD+UL. Then d≡s₀ modulo L and d≡1 modulo D.
4. No positive prime q divides both c and d. If q divides c but not L, it divides D, and d≡1 modulo q contradicts q∣d. If q divides L, reduce the unimodularity identity xr+ys=1 modulo q. Since c,d represent r,s modulo L and both are divisible by q, the reduced identity is 0=1 in ℤ/qℤ, impossible. Thus gcd(c,d)=1. Integer Bézout gives a,t with ad+tc=1. Set b=−t. The matrix M=((a,b),(c,d)) has determinant ad−bc=1 and bottom row reducing to (r,s). This proves the lifting fact for every positive L, including L=1.
5. Take arbitrary cosets AH_m and BH_n. Let (r_m,s_m) be the bottom row of A⁻¹ modulo m, and let (r_n,s_n) be the bottom row of B⁻¹ modulo n. Each is unimodular: for a determinant-one matrix ((a,b),(c,d)), the equality (−b)c+ad=1 supplies witnesses for its bottom row.
6. Apply the ring isomorphism from step 1 to assemble r_m,r_n into r∈ℤ/Kℤ and s_m,s_n into s∈ℤ/Kℤ. Assemble their two pairs of unimodularity witnesses into x,y∈ℤ/Kℤ as well. The image of xr+ys is (1,1), so injectivity of the isomorphism gives xr+ys=1. Steps 3–4 provide M∈SL₂(ℤ) whose bottom row reduces to (r,s).
7. Modulo m, the bottom row of M equals that of A⁻¹. Therefore the bottom row of MA equals that of A⁻¹A, namely (0,1), so MA∈H_m. Similarly MB∈H_n. Put C=M⁻¹. Then C⁻¹A∈H_m and C⁻¹B∈H_n, giving CH_m=AH_m and CH_n=BH_n. Hence F(CH_K)=(AH_m,BH_n), proving surjectivity.
8. Let e be the equivalence defined by the bijection F. Every q∈Q_K has a representative A. For any g∈G, e(g·AH_K)=e(gAH_K)=(gAH_m,gAH_n)=g·(AH_m,AH_n)=g·e(AH_K). This proves the required equivariance.

## Key steps

1. Construct the CRT ring isomorphism by Bézout and prove simultaneous divisibility.
2. Identify Γ₀(mn) with Γ₀(m)∩Γ₀(n), obtaining an injective canonical coset map.
3. Construct primitive integer lifts of unimodular residue rows.
4. Assemble the inverse representatives' bottom rows and witnesses by CRT.
5. Lift the assembled row and invert the resulting matrix to prove surjectivity.
6. Check equivariance of the canonical map under left multiplication.

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
