# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.stratum_card-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put M = p^a. Because p is prime, M is positive and each residue modulo M has a unique representative m with 0 ≤ m < M. For any k ≤ a, the representatives divisible by p^k are exactly p^k t with 0 ≤ t < p^(a−k). Indeed, p^a = p^k p^(a−k), so division by the positive integer p^k gives the claimed bound and uniqueness. Thus there are p^(a−k) such residues.
2. Take k = j and k = j+1, which are both at most a. The second set is contained in the first, and removing it leaves exactly the required stratum. Its cardinality is p^(a−j) − p^(a−j−1). Put b = a−j; since j < a, b ≥ 1. The cardinality is therefore p^(b−1)(p−1).
3. For any c ≥ 1, a natural number is coprime to p^c exactly when it is not divisible by p, by primality of p. Among the p^c representatives from 0 through p^c−1, exactly p^(c−1) are divisible by p. The definition of Euler’s totient consequently gives φ(p^c) = p^c − p^(c−1) = p^(c−1)(p−1).
4. If 2j ≤ a, then min(j,a−j) = j and b−1 = (j−1)+(a−2j), since j ≥ 1. The expression from step 2 is therefore p^(j−1)(p−1) p^(a−2j) = φ(p^j) p^(a−2j), by step 3. This is the claimed right-hand side.
5. If a < 2j, then min(j,a−j) = a−j = b and the truncated difference a−2j is zero. The proposed right-hand side is consequently φ(p^b) · 1 = p^(b−1)(p−1), again by step 3, agreeing with step 2. The two cases exhaust all possibilities and establish the required cardinality.

## Key steps

1. Parametrize multiples of p^k modulo p^a uniquely by t < p^(a−k).
2. Subtract the counts for k = j and k = j+1.
3. Count residues coprime to p^c to obtain φ(p^c) = p^(c−1)(p−1).
4. Split at 2j ≤ a to express the cardinality as φ(p^min(j,a−j)) times p^(a−2j).

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
