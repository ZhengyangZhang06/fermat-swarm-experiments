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
