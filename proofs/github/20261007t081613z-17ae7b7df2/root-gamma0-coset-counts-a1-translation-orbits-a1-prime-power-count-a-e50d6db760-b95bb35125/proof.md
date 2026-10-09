# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1.unit_iterate_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a prime p, a natural number a with 1 ≤ a, and z in R = ZMod(p^a) with p dividing m = z.val. Put M = p^a, which is positive, and D_n = 1+nz. The natural-number cast of m in R equals z.
2. For each natural n, set b = 1+n m. Because p divides n m, it cannot divide b: otherwise it would divide b-n m = 1, contradicting p ≥ 2. Thus b is coprime to p, and hence to M = p^a. Choose integers s,t with s b+t M = 1. Reduction modulo M gives (s : R)D_n = 1; commutativity gives the reverse product too. Therefore D_n is a unit. The ZMod inverse of a unit is its unit inverse, so D_n D_n⁻¹ = D_n⁻¹ D_n = 1.
3. Define F(w) = w(1+w)⁻¹. Prove (F^[n])(z) = z D_n⁻¹ by induction on n. At n=0, F^[0] is the identity and D_0 = 1, so the claimed equality holds.
4. Suppose the equality holds at n and write x = z D_n⁻¹. Since D_(n+1) = D_n+z, distributing multiplication and using D_n D_n⁻¹ = 1 gives 1+x = D_(n+1)D_n⁻¹. The element E = D_n D_(n+1)⁻¹ is a two-sided inverse of this product: each product with E reduces, by commutativity and the two unit cancellation identities, to 1. Thus 1+x is a unit and its ZMod inverse is E by uniqueness of inverses.
5. Consequently F(x) = z D_n⁻¹ D_n D_(n+1)⁻¹ = z D_(n+1)⁻¹. The recursion for function iteration completes the induction. Together with step 2 this gives both claimed conclusions for every n.

## Key steps

1. Represent z by m and show p does not divide 1+n m.
2. Use coprimality and Bezout to prove every denominator D_n is a unit.
3. Establish the iterate formula at n = 0.
4. Express 1+zD_n⁻¹ as D_(n+1)D_n⁻¹ and identify its inverse explicitly.
5. Cancel unit factors to complete the induction.

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
