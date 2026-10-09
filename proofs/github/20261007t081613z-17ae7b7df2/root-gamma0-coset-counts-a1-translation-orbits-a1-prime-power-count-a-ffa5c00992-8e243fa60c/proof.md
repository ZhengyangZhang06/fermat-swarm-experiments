# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.translation_charts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Set M = p^a. Since p is prime and a ≥ 1, M > 1 and p divides M. An element x of R is a unit exactly when p does not divide x.val: if p does not divide this representative, it is coprime to M and a Bezout identity supplies an inverse; if p divides it, reduction modulo p sends x to zero and precludes an inverse. Reduction modulo p sends x to zero exactly when p divides x.val.
2. Write a determinant-one integer matrix α as ((A,B),(C,D)). Its bottom row (r,s) modulo M is unimodular, since (-B)r + As = 1. At least one of r,s is a unit: otherwise their reductions modulo p are both zero, contradicting this identity. Common multiplication by a unit preserves unimodularity, with the witnesses multiplied by the inverse unit.
3. Every such row has a unique normalized form of one of two kinds. If r is a unit, scale by r⁻¹ to obtain (1,t), with t = r⁻¹s. Otherwise s is a unit, and scaling by s⁻¹ gives (z,1), with z = s⁻¹r and p dividing z.val. The two kinds cannot be related by a unit scaling, since their first coordinates are respectively a unit and a nonunit. Two normalized rows of the same kind related by a unit scaling have scaling factor 1, by comparing their coordinate equal to 1, so their parameters agree. Unit scaling preserves the kind and these normalized parameters.
4. For matrices α,β, the cosets α⁻¹H and β⁻¹H agree exactly when their bottom rows modulo M are related by a unit scaling. Indeed, equality of the cosets gives η = βα⁻¹ ∈ H and β = ηα. Modulo M the bottom-left entry of η is zero, and det η = 1 gives η₁₁η₂₂ = 1. Thus η₂₂ is a unit and the bottom row of β is η₂₂ times that of α. Conversely, if the rows are (r,s) and (r′,s′) = u(r,s), then the bottom-left entry of βα⁻¹ modulo M is r′s - s′r = 0. Hence βα⁻¹ ∈ H and the cosets agree.
5. Define e on the coset α⁻¹H by the normalized bottom row of α, recording (1,t) as inl t and (z,1) as inr z. Steps 3 and 4 make this well defined and injective. For surjectivity, choose integer representatives t̃ and z̃. The determinant-one matrices ((0,-1),(1,t̃)) and ((1,0),(z̃,1)) have the required normalized bottom rows. Their inverse cosets map respectively to inl t and inr z. Therefore e is a bijection, and thus an equivalence with inverse e⁻¹.
6. Left multiplication by T⁻¹ sends α⁻¹H to (αT)⁻¹H. Right multiplication of α by T sends its bottom row (r,s) to (r,r+s). This operation respects common unit scaling, so its effect may be computed using the normalized rows. On (1,t) it gives (1,t+1). Applying the definition of e proves the first required identity for every t.
7. On (z,1), with z ∈ B, the new row is (z,1+z). Its second coordinate reduces to 1 modulo p and is therefore a unit by step 1. Normalization gives (w,1), where w = z(1+z)⁻¹; the ZMod inverse here is the inverse of that unit. Reducing w modulo p gives zero, so p divides w.val and w ∈ B. This w satisfies both assertions required in the second identity, completing the proof.

## Key steps

1. Characterize units modulo p^a by nondivisibility by p.
2. Normalize unimodular rows uniquely into disjoint forms (1,t) and (z,1) with p dividing z.val.
3. Identify equality of inverse cosets with common unit scaling of bottom rows.
4. Construct the bijection and prove surjectivity using explicit determinant-one matrices.
5. Compute T⁻¹ on inverse cosets by right multiplication by T, obtaining t ↦ t+1 and z ↦ z(1+z)⁻¹.

## Reference use

### local-project

Queries:
- `unimodular|ProjectiveLine|cusp|orbit|zpow`
- `isUnit_iff_coprime|val_lt|mul_inv_of_unit|inv_mul_of_unit|isUnit.*pow|isUnit.*iff|natCast.*val|natCast_eq_zero|val_natCast`
- `totient_prime_pow|totient_one|card|orbitRel|mem_Gamma0|def Gamma0|eq_iff`
- `prime_power.*(orbit|chart)|valuation.*strat|translation.*chart|fractional.*(iterat|period)`
- `p10_17ae7b7d_pp_translation_charts|p10_17ae7b7d_pp_fractional_iterates|p10_17ae7b7d_pp_stratum_card`
- `python3 .humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/prime-power-split-ipfffwyj/run.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Totient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/prime-power-split-ipfffwyj/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/prime-power-split-ipfffwyj/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/prime-power-split-ipfffwyj/report.json`

The snapshots match project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; both snapshots and all nine pinned dependency checkouts are clean. Relevant infrastructure includes ZMod.isUnit_natCast_iff_not_dvd_pow, ZMod.inv_coe_unit, ZMod.mul_inv_of_unit, Nat.totient_prime_pow, the Gamma0 membership definition, and coset-action/orbit equivalences. No matching chart, fractional-period, or valuation-stratum theorem was found. The separate projective-line module supplies useful definitions but is absent under the frozen imports; the proposed types avoid those unavailable declarations. All three exact types elaborate after import Submission from proof-base c77074cc2682d4bf219f2909b6b4767445f7f7bc in the disposable compiler copy. Reflexivity probes verify left coset multiplication, function iteration, and matrix multiplication. Proposed names have no collisions in the DAG, node records, Submission, or imported environment. Audited interfaces and library lemmas depend only on propext, Classical.choice, and Quot.sound. Header-policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 matched; only listed lines 10–12 were omitted, and Lean verified all 56 targets absent. The report records exact omissions, reversible reconstruction, and original/build hashes. The original contract and working tree remain unchanged. These are interface diagnostics, not comparator acceptance of theorem proofs.
