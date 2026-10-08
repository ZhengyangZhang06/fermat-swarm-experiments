# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.gamma0_coset_counts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Since N≠0, N>0. If N=1, the defining congruence for Γ₀(N) is automatic, so H=G and Q is a singleton. The residue ring ℤ/ℤ has one element, and both polynomial root sets are singletons. The only positive divisor is 1, giving μ=c=1. Every assertion follows. Assume henceforth N>1.

2. First compute on right cosets Hα. Right multiplication R_B(Hα)=HαB is well-defined and has inverse R_{B⁻¹}. Inversion Hα↦α⁻¹H bijects these cosets with Q and intertwines R_B with left multiplication by B⁻¹. A permutation and its inverse have the same fixed points and generated orbits. Thus it suffices to count right cosets and the fixed points and cycles of R_S, R_U, R_T, where U=ST.

3. Let R=ℤ/Nℤ. A row (r,s) is unimodular when xr+ys=1 for some x,y∈R. Identify two such rows when one is a common unit multiple of the other. The bottom row of a determinant-one integer matrix is unimodular modulo N, by its determinant equation. If η∈H, its bottom row modulo N is (0,d), with d a unit because its diagonal entries multiply to 1. Hence left multiplication by η scales bottom rows by a unit. This defines a map from right cosets to unimodular row classes. If β and α have bottom rows related by (r′,s′)=u(r,s), then the bottom-left entry of βα⁻¹ is r′s−s′r=0 modulo N. By the defining Γ₀ membership criterion, βα⁻¹∈H, so Hβ=Hα. The map is injective.

4. We record the elementary Chinese remainder argument needed for surjectivity and counting. For coprime positive integers a,b, the Euclidean algorithm and backward substitution give ua+vb=1. Prescribed residues A modulo a and B modulo b are simultaneously represented by Avb+Bua. If a and b both divide n=at, the same identity multiplied by t shows b∣t, hence ab∣n. Therefore the representative is unique modulo ab. Coprimality with each of two integers implies coprimality with their product, by multiplying Bézout identities. Induction gives the residue bijection for finitely many pairwise coprime moduli. Since reduction respects addition and multiplication, this is a ring isomorphism.

5. To lift a unimodular row (r,s), choose an integer D representing s with 1≤D≤N. Choose C representing r modulo N and congruent to 1 modulo every prime dividing D but not N. These finitely many prime moduli are pairwise coprime and coprime to N, so step 4 supplies C. A prime dividing D and N cannot divide C: reduction of the unimodularity equation modulo that prime would otherwise give 0=1. A prime dividing D but not N cannot divide C by construction. Thus C and D have no common prime divisor. Any common divisor greater than 1 would have a prime divisor, obtained by taking its least divisor greater than 1; therefore gcd(C,D)=1. Choose x,y∈ℤ with xC+yD=1. The matrix with rows (y,−x) and (C,D) has determinant 1 and lifts the row. This proves surjectivity. In particular the right-coset set, and hence Q, is finite because the row classes form a quotient of a finite set.

6. For a prime p and a≥1, a residue modulo pᵃ is a unit exactly when it is not divisible by p. Necessity follows by reduction modulo p; sufficiency follows from Bézout with pᵃ. A row is unimodular exactly when at least one coordinate is a unit: a unit coordinate supplies the combination, whereas if both coordinates are divisible by p, every combination is divisible by p. Every class has exactly one representative in one of two disjoint charts: [1:t] with arbitrary t, or [s:1] with p∣s. Normalize the first coordinate when it is a unit and otherwise normalize the second. The coordinate 1 forces uniqueness within either chart, and divisibility of the first coordinate separates them. Their sizes are pᵃ and p^{a−1}.

7. Factor N as a product of distinct prime powers. Existence of this factorization follows by induction, splitting a composite integer into smaller factors. For uniqueness, Euclid's lemma follows from Bézout: if p∤a, multiplication of a Bézout identity for p,a by b shows that p∣ab implies p∣b. Repeated cancellation then proves uniqueness. Chinese remaindering identifies R with the product of the prime-power rings. Unimodularity, units, and common unit scaling are componentwise conditions because their witnesses project and assemble. Hence the row-class cardinality is ∏_{pᵃ∥N}(pᵃ+p^{a−1}). Expanding this product, choosing the smaller term for a subset of primes contributes N/d for the corresponding squarefree divisor d. Thus the cardinality is μ.

8. Matrix multiplication gives R_S(r,s)=(s,−r), R_U(r,s)=(s,s−r), and R_T(r,s)=(r,r+s). An S-fixed row class satisfies s=ur and −r=us for a unit u. Substitution in xr+ys=1 gives (x+yu)r=1, so r is a unit. Normalize to [1:t]. The equations become u=t and t²+1=0. Conversely, a root t has inverse −t and satisfies (t,−1)=t(1,t), so its row class is fixed. Unique normalization gives a bijection with the e₂ roots.

9. A U-fixed class satisfies s=ur and s−r=us for a unit u. The same unimodularity calculation makes r a unit. Normalization to [1:t] gives t²−t+1=0. Conversely, this equation gives t(1−t)=1 and (t,t−1)=t(1,t), proving fixedness. Substitution x=−t bijects these roots with those of x²+x+1=0. The U-fixed count is therefore e₃.

10. Modulo pᵃ, T sends [1:t] to [1:t+1], making the first chart one cycle of length pᵃ. On the second chart it sends s to s/(1+s). Every 1+ns is a unit because p∣s. Induction gives the nth iterate s/(1+ns), which equals s exactly when ns²=0 modulo pᵃ. Multiplication by the denominator's inverse preserves the valuation of s, so each valuation stratum is invariant.

11. For a nonzero second-chart residue write s=pʲv with 1≤j<a and v a unit. The return condition is pᵃ∣np^{2j}, equivalently p^{max(a−2j,0)}∣n. Thus every element in this stratum has cycle length p^{max(a−2j,0)}. There are p^{a−j}−p^{a−j−1} elements in the stratum. Dividing by the common cycle length gives pʲ−p^{j−1} when 2j<a, and p^{a−j}−p^{a−j−1} otherwise. This is φ(p^{min(j,a−j)}): for b≥1, precisely p^{b−1} residues modulo pᵇ are divisible by p, so φ(pᵇ)=pᵇ−p^{b−1}. The first-chart cycle supplies the j=0 term, and s=0 supplies the j=a term, each equal to φ(1)=1. The local number of cycles is therefore ∑_{j=0}^a φ(p^{min(j,a−j)}).

12. Under Chinese remaindering T acts componentwise. Choose one cycle in each prime-power component. Their lengths are powers of distinct primes, possibly 1, hence pairwise coprime. Applying step 4 to the iteration number reaches every tuple of positions in these cycles. Their product is one global cycle, and these products partition the row-class set. For d=∏pʲ dividing N=∏pᵃ, one has gcd(d,N/d)=∏p^{min(j,a−j)}. Bézout identifies units modulo a positive integer with the coprime residue classes counted by φ; Chinese remaindering identifies these units componentwise, proving multiplicativity of φ for coprime arguments. Expanding the product of the local cycle counts consequently gives ∑_{d∣N}φ(gcd(d,N/d))=c. Finally transfer all counts through inversion from step 2. On a finite set the subgroup generated by T has precisely the permutation cycles as its orbits, since inverse iteration adds no new points. This proves the exact statement.

## Key steps

1. Handle N=1 and transfer left-coset questions to right cosets by inversion.
2. Identify right cosets with unimodular residue rows modulo unit scaling.
3. Prove row lifting using Bézout and Chinese remaindering.
4. Count prime-power charts and expand their product to obtain dedekindPsi.
5. Identify S- and ST-fixed classes with the two polynomial root sets.
6. Compute translation periods and cycle counts in each prime-power chart.
7. Assemble cycles using coprime lengths and identify the totient divisor sum.
8. Transfer the counts to the exact quotient action and orbit relation.

## Reference use

### local-project

Queries:
- `rg -n 'def (genusFormula|nuTwo|nuThree|cuspCount|dedekindPsi)|valence|gamma0_coset_counts|periodic_disk_extension|gamma0_norm_vanishing|level_one_valence_inequality' <snapshot>/project/Definitions <snapshot>/mathlib/Mathlib/NumberTheory/ModularForms`
- `analyticOrderAt_eq_natCast|analyticOrderNatAt_eq_iff|theorem DifferentiableOn.analyticAt|isExactOn_ball|exp_two_pi_mul_I_mul_div_eq_one_iff|exp_eq_exp_iff_exists_int|isZeroAtImInfty_iff|mdifferentiable_iff|SL_slash_def|SL_slash_apply|def IsZeroAt|def IsCusp|def IsParabolic|integral_eq_sub_of_hasDerivAt_of_le`
- `gamma0_coset_counts|periodic_disk_extension|gamma0_norm_vanishing|level_one_valence_inequality|theorem.*[Vv]alence|lemma.*[Vv]alence`
- `rg -n --hidden --no-ignore -g dag.json 'p10_17ae7b7d_(gamma0_coset_counts|periodic_disk_extension|gamma0_norm_vanishing|level_one_valence_inequality)' /mnt/data/zhengyang-workspace/fermat-swarm-projects`
- `git rev-parse HEAD; git status --porcelain --untracked-files=no`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o TargetAbsence.olean TargetAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o ChildTypes.olean ChildTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Algebra/Group/Subgroup/Actions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.agents/skills/frozen-header-policy-evidence/evidence.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/operator-approved-header-policy-20261008/controller-compatibility-report.json`
- `/tmp/p10-split-interface-5bnnjwsk/report.json`
- `/tmp/p10-split-interface-5bnnjwsk/TargetAbsence.lean`
- `/tmp/p10-split-interface-5bnnjwsk/ChildTypes.lean`
- `/tmp/p10-split-interface-5bnnjwsk/ChildTypes.log`

The snapshot pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; fresh Git checks matched both revisions and found clean tracked snapshot trees and all nine dependency checkouts matching their pins. The numerical definitions, quotient actions, real-image subgroup coercion, cusp condition, and analytic-order interfaces match the proposed statements. Searches found no existing versions of the four helpers or a named valence theorem in the searched Definitions and modular-form sources, and no conflicting helper-name reservation in the local DAGs. All four literal types compiled after import Submission in a fresh disposable context. Reflexivity probes verified left multiplication on cosets, restriction to the subgroup generated by T, the real-image coercion, and matrix multiplication for S*T. The four type definitions and the selected imported declarations reported only propext, Classical.choice, and Quot.sound. Policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 was checked against its matching entry. Only original lines 10–12 were omitted in the disposable compiler copy; Lean confirmed all 56 targets absent. Original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and derived hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539 were recorded with exact omitted lines and reversible reconstruction. Original contract and Submission remained byte-identical. These are interface diagnostics, not child-proof or comparator acceptance.
