<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1 -->

## Theorem `Submission.p10_17ae7b7d_pp_fractional_iterates`

Let p be prime, let a,j be natural numbers with 1 ≤ j < a, and let z ∈ R = Z/(p^a)Z satisfy p^j | z.val and p^(j+1) ∤ z.val. Define F(w) = w(1+w)⁻¹ using the ZMod inverse. For every natural number n, 1+nz is a unit, F^n(z) = z(1+nz)⁻¹, F^n(z) = z if and only if p^(a−2j) divides n, and F^n(z) still has exact valuation j: p^j divides its canonical representative and p^(j+1) does not. The exponent a−2j is truncated natural subtraction.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/452

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/502, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/503, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/504

## Lean problem

Declaration: `Submission.p10_17ae7b7d_pp_fractional_iterates`

```lean
∀ (p a j : ℕ), Nat.Prime p → 1 ≤ j → j < a → ∀ z : ZMod (p ^ a), p ^ j ∣ z.val → ¬ p ^ (j + 1) ∣ z.val → let F : ZMod (p ^ a) → ZMod (p ^ a) := fun w => w * (1 + w)⁻¹; ∀ n : ℕ, IsUnit (1 + (n : ZMod (p ^ a)) * z) ∧ (F^[n]) z = z * (1 + (n : ZMod (p ^ a)) * z)⁻¹ ∧ ((F^[n]) z = z ↔ p ^ (a - 2 * j) ∣ n) ∧ p ^ j ∣ ((F^[n]) z).val ∧ ¬ p ^ (j + 1) ∣ ((F^[n]) z).val
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

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put M = p^a and m = z.val. The hypotheses give m = p^j v for a natural number v not divisible by p: divisibility supplies v, and p | v would contradict p^(j+1) ∤ m. In particular m is nonzero, p divides m, and a ≥ 2. Since p is prime, v and v² are coprime to M.
2. For each n ≥ 0 put D_n = 1+nz in R. Since z reduces to zero modulo p, D_n reduces to 1 modulo p. Its canonical representative is consequently not divisible by p, and hence is coprime to p^a. A Bezout identity shows D_n is a unit. The ZMod inverse D_n⁻¹ is its unit inverse, so both D_n D_n⁻¹ and D_n⁻¹ D_n equal 1.
3. Prove F^n(z) = zD_n⁻¹ by induction on n. For n = 0 this follows from D_0 = 1. If the identity holds for n, then 1+F^n(z) = 1+zD_n⁻¹ = D_(n+1)D_n⁻¹. This is a unit whose inverse is D_n D_(n+1)⁻¹. Therefore F(F^n(z)) = zD_n⁻¹ D_n D_(n+1)⁻¹ = zD_(n+1)⁻¹, proving the induction step.
4. For k ≤ a, reduction R → Z/(p^k)Z is well defined, and its value on x is zero exactly when p^k divides x.val. Multiplication by a unit preserves this kernel in both directions, since the image of a unit is invertible. Apply this observation to x = z and the unit D_n⁻¹, first with k = j and then with k = j+1, both at most a. By step 3 it follows that p^j divides (F^n(z)).val and p^(j+1) does not.
5. Since D_n is a unit, step 3 gives F^n(z) = z if and only if z = zD_n. Expanding D_n, this is equivalent to nz² = 0 in R, and hence to M dividing n m² as an integer. Substituting m = p^j v and cancelling the coprime factor v² gives the equivalent condition p^a | n p^(2j). This cancellation follows, for example, by multiplying a Bezout identity for v² and M by n p^(2j).
6. If 2j < a, write p^a = p^(2j) p^(a−2j) and cancel the positive integer p^(2j); the condition is exactly p^(a−2j) | n. If a ≤ 2j, then p^a divides p^(2j), so the condition holds for every n. In this case truncated subtraction gives a−2j = 0 and p^(a−2j) = 1, which also divides every n. This proves the stated return criterion in all cases. Together with steps 2, 3 and 4, it proves all four conclusions for every n.

## Key steps

1. Write the canonical representative as p^j v with p not dividing v.
2. Show every denominator 1+nz is a unit by reduction modulo p.
3. Inductively compute F^n(z) = z(1+nz)⁻¹ using only unit cancellations.
4. Use reduction modulo p^j and p^(j+1) to preserve exact valuation under unit multiplication.
5. Convert the return condition to p^a | n p^(2j) and distinguish 2j < a from a ≤ 2j.

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


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/618

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
