# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1.unit_mul_dvd_val-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix natural numbers M,d with M>0 and d dividing M, elements x,u of ZMod M, and assume u is a unit. Since 0 does not divide the positive number M, d>0.
2. Reduction of integer representatives modulo d gives a ring homomorphism ρ : ZMod M → ZMod d: two representatives of the same class modulo M differ by a multiple of M and therefore by a multiple of d. For every y in ZMod M, ρ(y) is the class of y.val modulo d. Consequently ρ(y)=0 if and only if d divides y.val.
3. Because u is a unit, there is v in ZMod M with uv=vu=1. Applying ρ gives ρ(u)ρ(v)=ρ(v)ρ(u)=1. If d divides x.val, then ρ(x)=0, so ρ(xu)=ρ(x)ρ(u)=0 and d divides (xu).val.
4. Conversely, if d divides (xu).val, then ρ(x)ρ(u)=0. Multiplication by ρ(v) yields ρ(x)=0, whence d divides x.val. These two implications prove the required equivalence, also when d=1.

## Key steps

1. Construct reduction modulo d using d ∣ M.
2. Identify its kernel with divisibility of canonical representatives by d.
3. Map a multiplicative inverse of u through the reduction homomorphism.
4. Prove both implications by multiplication and cancellation in ZMod d.

## Reference use

### local-project

Queries:
- `val_mul|isUnit_iff_coprime|isUnit_of_coprime|castHom|mul_inv_of_unit|inv_mul_of_unit`
- `dvd_val|val.*dvd.*mul|dvd.*val.*mul|iterate.*inv|inv.*iterate`
- `natCast_zmod_val|natCast_eq_zero_iff|val_natCast|cast_eq_val`
- `pow.*dvd.*pow|dvd.*mul.*iff|pow.*not_dvd|coprime_pow`
- `fractional.*iterat|unit_mul_dvd_val|square_annihilation|valuation.*strat`
- `p10_17ae7b7d_fi_unit_iterate_formula|p10_17ae7b7d_fi_unit_mul_dvd_val|p10_17ae7b7d_fi_square_annihilation`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-translation-orbits-a1-prime-power-count-a-ea38848b51/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Prime/Basic.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/fractional-split-0kqs_t14/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/fractional-split-0kqs_t14/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/fractional-split-0kqs_t14/report.json`

The handoff identifies this theorem as the depth-four fractional_iterates node. The reference snapshots match project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; both snapshots and all nine pinned dependencies are clean. Relevant infrastructure includes ZMod.isUnit_natCast_iff_not_dvd_pow, unit inverse identities, ZMod.castHom, representative-cast identities, ZMod.natCast_eq_zero_iff, and Nat.Prime.coprime_pow_of_not_dvd. The searches found no specialized fractional-iterate, unit-preservation, or square-annihilation theorem matching the searched patterns. All three proposed types elaborate after import Submission at proof-base 81e439ead62e72b45d1f96dd998a9b47a5b90960 in a disposable compiler copy. Reflexivity probes confirm function iteration, ZMod ring multiplication, the ZMod inverse, and the monoid used by IsUnit. The names are absent from the imported environment and active DAG reservations. Audited types and library declarations use only propext, Classical.choice, and Quot.sound. The policy digest matches 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; only listed lines 10–12 were omitted, and Lean confirmed all 56 targets absent. The report records exact omissions, reversible original/build hashes, and successful final diagnostics. The frozen contract remains unchanged. These checks establish interface compatibility, not comparator acceptance of the unimplemented child proofs.
