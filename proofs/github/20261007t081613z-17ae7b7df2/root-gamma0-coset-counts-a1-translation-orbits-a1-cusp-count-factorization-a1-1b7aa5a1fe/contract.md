<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1 -->

## Theorem `Submission.p10_17ae7b7d_to_cusp_count_factorization`

For every nonzero natural number N, let P be its finite set of prime divisors and let a_p be the exponent of p in N. Then ModularCurve.cuspCount N, defined as ∑_{d∣N} φ(gcd(d,N/d)), equals ∏_{p∈P} ∑_{j=0}^{a_p} φ(p^{min(j,a_p−j)}). The empty product for N = 1 is 1.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/420

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/512, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/513

## Lean problem

Declaration: `Submission.p10_17ae7b7d_to_cusp_count_factorization`

```lean
∀ (N : ℕ) [NeZero N], ModularCurve.cuspCount N = N.primeFactors.prod (fun p => (Finset.range (N.factorization p + 1)).sum (fun j => Nat.totient (p ^ min j (N.factorization p - j))))
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

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N ≠ 0. If N = 1, its only positive divisor is 1, so cuspCount 1 = φ(gcd(1,1)) = φ(1) = 1. Its set of prime factors is empty, and the proposed product is also 1. Assume N > 1.
2. Write N = ∏_{p∈P} p^{a_p}, where P is the finite set of distinct prime divisors and a_p = N.factorization p > 0. Existence of such a factorization follows by strong induction: a number greater than 1 is either prime or is a product of two smaller positive numbers. For uniqueness, a prime dividing a product divides one factor: if it does not divide the first factor, a Bézout identity for that factor and the prime, multiplied by the second factor, proves divisibility of the second. Applying this repeatedly and cancelling primes proves uniqueness of the exponents.
3. Consequently the positive divisors d of N are in bijection with exponent tuples (j_p)_{p∈P} satisfying 0 ≤ j_p ≤ a_p, by d = ∏_{p∈P} p^{j_p}. Every such product divides N. Conversely, factoring d and N/d and comparing their product with N shows that d has no other prime factors and has exactly such exponents. Uniqueness of factorization makes this parametrization injective. For the corresponding divisor, N/d = ∏_{p∈P} p^{a_p−j_p}; these subtractions are nonnegative because j_p ≤ a_p.
4. For this divisor, gcd(d,N/d) = ∏_{p∈P} p^{min(j_p,a_p−j_p)}. The product on the right divides both d and N/d. Every common divisor has, at each prime p, exponent at most both j_p and a_p−j_p, and no prime factor outside P; hence it divides that product. This proves the gcd identity.
5. Totient is multiplicative on coprime positive integers. To see this, a residue modulo a positive integer A is invertible exactly when its representative is coprime to A: Bézout gives an inverse in one direction, and an inverse congruence gives a Bézout identity in the other. For coprime A,B, choose uA+vB = 1. The integer xvB+yuA realizes any specified residues x modulo A and y modulo B. A number divisible by both A and B is divisible by AB, since Bézout allows cancellation of A modulo B. Thus reduction is a ring bijection modulo AB with the product of the residue rings modulo A and B. Inverses project and assemble, so this bijection restricts to a bijection on units. Counting units yields φ(AB) = φ(A)φ(B), including factors equal to 1.
6. The prime powers in the gcd product of step 4 have distinct prime bases, so they are pairwise coprime. Repeatedly applying step 5 gives φ(gcd(d,N/d)) = ∏_{p∈P} φ(p^{min(j_p,a_p−j_p)}).
7. Reindex the defining sum cuspCount N = ∑_{d∣N} φ(gcd(d,N/d)) using the bijection in step 3 and substitute step 6. The result is the sum, over all independent choices 0 ≤ j_p ≤ a_p, of ∏_{p∈P} φ(p^{min(j_p,a_p−j_p)}). Finite distributivity identifies this with ∏_{p∈P} ∑_{j=0}^{a_p} φ(p^{min(j,a_p−j)}): inductively, removing one prime separates its index choice from the remaining tuple, and distributing its finite sum gives precisely that factor times the remaining product. Replacing P and a_p by N.primeFactors and N.factorization p gives the stated Lean expression.

## Key steps

1. Handle N = 1 using the empty product.
2. Factor N uniquely into powers of its distinct prime divisors.
3. Parametrize divisors by bounded exponent tuples.
4. Compute gcd(d,N/d) by taking the minimum of the complementary exponents.
5. Prove totient multiplicativity by CRT on units.
6. Reindex the divisor sum and distribute it into the product of local sums.

## Reference use

### local-project

Queries:
- `cuspCount|genusFormula`
- `totient_mul|totient_prime_pow|chineseRemainder|prime_pow|isUnit_iff_coprime`
- `cuspCount.*(mul|prod|pow)|translation_orbits|orbit.*Gamma0|Gamma0.*orbit`
- `multiplicative_factorization|prod_pow_factorization|divisors.*prod|divisors_prime_pow`
- `def orbitRel|orbitRel_apply|orbitRel_iff|instance.*Quotient|smul_mk`
- `p10_17ae7b7d_to_(prime_power_count|coprime_count_mul|cusp_count_factorization)`
- `python3 /tmp/p10-translation-split-nhp6svxx/run.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-translation-orbits-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Totient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Factorization/Divisors.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Factorization/Induction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p10-translation-split-nhp6svxx/TargetAbsence.lean`
- `/tmp/p10-translation-split-nhp6svxx/ChildTypes.lean`
- `/tmp/p10-translation-split-nhp6svxx/ChildTypes.log`
- `/tmp/p10-translation-split-nhp6svxx/statements.json`
- `/tmp/p10-translation-split-nhp6svxx/report.json`

The clean reference snapshots match project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine dependency checkouts matched their pins and had clean tracked files. Relevant infrastructure includes ZMod.chineseRemainder, the prime-power unit criterion, totient formulas, divisor parametrization by factorization, and left coset actions. No matching orbit-count or cuspCount product formula was found. The separate projective-line module is outside the frozen imports, so no child type references its declarations. All three exact child types elaborated after import Submission in the disposable compiler context. Reflexivity probes verified left coset multiplication, subgroup restriction, and matrix multiplication. Proposed names had no matches in the local records or imported environment. Interface definitions and audited library declarations use only propext, Classical.choice, and Quot.sound. The matching header-policy digest was 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; only lines 10–12 were omitted, and Lean verified all 56 targets absent. The report records exact omissions, reversible reconstruction, original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and build hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539. The frozen contract and original Submission header remain unchanged. These checks establish interface compatibility, not comparator acceptance of theorem proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
