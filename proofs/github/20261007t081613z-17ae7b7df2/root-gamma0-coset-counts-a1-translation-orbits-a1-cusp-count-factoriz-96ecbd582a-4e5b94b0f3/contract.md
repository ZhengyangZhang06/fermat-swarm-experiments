<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1.cusp_count_coprime_mul-a1 -->

## Theorem `Submission.p10_17ae7b7d_ccf_coprime_mul`

For all natural numbers m and n with gcd(m,n) = 1, ModularCurve.cuspCount (m*n) = ModularCurve.cuspCount m * ModularCurve.cuspCount n. Here cuspCount t is the sum of φ(gcd(d,t/d)) over d in Nat.divisors t; for positive t these are its positive divisors, and Nat.divisors 0 is empty.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1.cusp_count_coprime_mul-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/454

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_ccf_coprime_mul`

```lean
∀ (m n : ℕ), Nat.Coprime m n → ModularCurve.cuspCount (m * n) = ModularCurve.cuspCount m * ModularCurve.cuspCount n
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
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1.cusp_count_coprime_mul-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write C(t) for ModularCurve.cuspCount t. Since Nat.divisors 0 is empty, C(0) = 0. If m = 0 or n = 0, the asserted equality has both sides zero. Henceforth assume m and n are positive and coprime.
2. For each prime q, let α_q and β_q be its exponents in m and n. Coprimality implies that at least one of these exponents is zero. If d divides mn, its exponent e_q satisfies e_q ≤ α_q + β_q. Set a = gcd(d,m) and b = gcd(d,n). Their exponents are min(e_q,α_q) and min(e_q,β_q), whose sum is e_q because one of α_q,β_q is zero. Unique prime factorization therefore gives d = ab, with a dividing m and b dividing n. Conversely, a dividing m and b dividing n implies ab divides mn. The prime supports of m and n are disjoint, so the exponents of ab recover separately the exponents of a and b. Thus the representation is unique, giving a bijection between divisors of mn and pairs of divisors of m and n.
3. Fix such a pair a,b and set A = m/a and B = n/b. These numbers are positive, m = aA, and n = bB. Consequently (mn)/(ab) = AB by cancellation. Put g = gcd(a,A) and h = gcd(b,B). At a prime dividing m, the exponents in b and B are zero. The exponent in gcd(ab,AB) is therefore min(v_q(a),v_q(A)), exactly the exponent in g, while its exponent in h is zero. At a prime dividing n the same argument interchanges the roles. At any other prime all these exponents vanish. Unique factorization gives gcd(ab,AB) = gh. Moreover g divides m and h divides n, so g and h are coprime.
4. For positive coprime g,h, Euler's totient satisfies φ(gh) = φ(g)φ(h). To verify this, choose integers u,v with ug + vh = 1. Reduction from residues modulo gh to pairs of residues modulo g and h is surjective: xvh + yug has prescribed residues x and y. It is injective: if g and h divide z, write z = gk; multiplying ug + vh = 1 by k shows that h divides k, hence gh divides z. Reduction is therefore a ring isomorphism. It restricts to a bijection on units, since inverses project and a pair of inverses lifts to an inverse by injectivity. A residue is a unit exactly when its representative is coprime to the modulus: Bézout supplies an inverse, and an inverse congruence supplies a Bézout identity. Counting units proves the totient formula, also when either modulus is 1. Applying it to step 3 yields φ(gcd(ab,(mn)/(ab))) = φ(gcd(a,m/a))φ(gcd(b,n/b)).
5. Reindex the defining sum for C(mn) by the bijection in step 2 and substitute step 4. It becomes the double sum over a dividing m and b dividing n of φ(gcd(a,m/a))φ(gcd(b,n/b)). Finite distributivity separates this double sum into the product of the two defining sums C(m) and C(n). Together with the zero cases in step 1, this proves the stated equality for all natural m,n satisfying the coprimality hypothesis.

## Key steps

1. Handle zero levels using the empty divisor finset.
2. Use disjoint prime supports to biject divisors of mn with pairs of divisors of m and n.
3. Compute the complementary quotient and split its gcd into coprime factors.
4. Apply totient multiplicativity, justified by the Chinese remainder bijection on units.
5. Reindex the divisor sum and separate the double sum by finite distributivity.

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
