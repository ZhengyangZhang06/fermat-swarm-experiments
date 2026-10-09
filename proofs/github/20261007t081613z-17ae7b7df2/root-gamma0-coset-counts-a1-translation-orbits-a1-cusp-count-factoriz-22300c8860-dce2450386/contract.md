<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1.cusp_count_prime_power-a1 -->

## Theorem `Submission.p10_17ae7b7d_ccf_prime_power`

For every prime natural number p and every natural exponent a, ModularCurve.cuspCount (p^a) equals the sum of φ(p^min(j,a−j)) over j = 0,…,a. Here cuspCount t is the sum of φ(gcd(d,t/d)) over positive divisors d of t, and subtraction in the exponent is natural-number subtraction. The statement includes a = 0.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1.cusp_count_prime_power-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/454

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_ccf_prime_power`

```lean
∀ (p a : ℕ), Nat.Prime p → ModularCurve.cuspCount (p ^ a) = (Finset.range (a + 1)).sum (fun j => Nat.totient (p ^ min j (a - j)))
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

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1.cusp_count_prime_power-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a prime p and a natural exponent a. Since p ≥ 2, p^a is positive. Every positive divisor d of p^a has no prime factor other than p, and its exponent j of p is at most a. Thus d = p^j for some 0 ≤ j ≤ a. Conversely, each such p^j divides p^a. Powers of p are strictly increasing in the exponent, so these representations are unique. This gives a bijection from Finset.range (a + 1) to the positive divisors of p^a.
2. For an exponent j in this range, j ≤ a and j + (a−j) = a. Hence p^a = p^j * p^(a−j). Since p^j is positive, exact division gives p^a / p^j = p^(a−j).
3. If j ≤ a−j, then p^j divides p^(a−j), so their gcd is p^j. If a−j ≤ j, the reverse divisibility makes their gcd p^(a−j). Therefore in all cases gcd(p^j,p^a/p^j) = p^min(j,a−j).
4. Reindex the defining divisor sum for cuspCount(p^a) using the bijection in step 1. Replace each complementary quotient and gcd using steps 2 and 3, and apply totient to the resulting identity. The sum is exactly the asserted sum over Finset.range (a + 1). When a = 0, this range consists only of j = 0, and both sides are φ(1) = 1, so the proof includes the zero exponent.

## Key steps

1. Parametrize the divisors of p^a uniquely by p^j with j ≤ a.
2. Compute the complementary quotient as p^(a−j).
3. Evaluate the gcd of the two powers using the minimum exponent.
4. Substitute into the divisor sum, including the case a = 0.

## Reference use

### local-project

Queries:
- `cuspCount|genusFormula|sum_divisors|prod_primeFactors|prod.*sum.*factorization`
- `gcd|prod_prime|prod.*factorization|totient_mul|sum_mul|sum_prod|IsMultiplicative`
- `theorem multiplicative_factorization|lemma multiplicative_factorization|gcd_pow_min|gcd_mul_gcd`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Factorization/Divisors.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Factorization/Induction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Totient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/Divisors.lean`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. GenusNumerics defines the exact divisor sum and proves cuspCount_one; the project search found no existing cusp-count multiplicativity or prime-power evaluation theorem. Mathlib supplies divisor parametrization by bounded factorizations, Nat.multiplicative_factorization, Nat.totient_mul, and Nat.sum_divisors_prime_pow. The proposed types elaborate with the pinned toolchain, and the checked arithmetic infrastructure has only propext, Classical.choice, and Quot.sound as transitive axioms.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
