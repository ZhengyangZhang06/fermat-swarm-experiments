<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1.unit_iterate_formula-a1 -->

## Theorem `Submission.p10_17ae7b7d_fi_unit_iterate_formula`

Let p be prime, let a be a natural number with 1 ≤ a, and let z ∈ R = ZMod(p^a) satisfy p ∣ z.val. Define F : R → R by F(w) = w(1+w)⁻¹, using the ZMod inverse. For every natural n, the element 1+nz is a unit and F^n(z) = z(1+nz)⁻¹. Natural numbers in ring expressions are cast into R.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1.unit_iterate_formula-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/483

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_fi_unit_iterate_formula`

```lean
∀ (p a : ℕ), Nat.Prime p → 1 ≤ a → ∀ z : ZMod (p ^ a), p ∣ z.val → let F : ZMod (p ^ a) → ZMod (p ^ a) := fun w => w * (1 + w)⁻¹; ∀ n : ℕ, IsUnit (1 + (n : ZMod (p ^ a)) * z) ∧ (F^[n]) z = z * (1 + (n : ZMod (p ^ a)) * z)⁻¹
```

### Frozen project context

`Fermat/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean` at `a97febc53b1c4d489edc54ca44132af7a21279b3` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.CuspSpace.cuspDenomAux_infty
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one

set_option autoImplicit false

theorem CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero (N : ℕ) [NeZero N]
    (hg : ModularCurve.genusFormula N = 0) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f = 0 := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

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


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/601

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
