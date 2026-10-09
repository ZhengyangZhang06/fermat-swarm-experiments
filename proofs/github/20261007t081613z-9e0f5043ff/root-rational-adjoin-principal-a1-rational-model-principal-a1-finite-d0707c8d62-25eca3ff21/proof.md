# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1.polynomial_exponent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write R = Polynomial K. Irreducibility implies q ≠ 0 and q is not a unit. A nonzero polynomial of natural degree zero is a nonzero constant and is a unit over K, so d = natDegree q > 0. Also q does not divide 1, since a divisor of 1 is a unit.
2. If q does not divide a, the gcd g of q and a is a unit: write q = g h, and use irreducibility to conclude that g or h is a unit. If g were not a unit, h would be a unit, making q associated to g; then g dividing a would force q to divide a. A Bezout identity for g, multiplied by its inverse, therefore gives u q + v a = 1. If q divides a b, multiplying this identity by b shows q divides b. Consequently q divides a product only if it divides one of the factors.
3. Prove by strong induction on natDegree a that every nonzero a has a factorization a = q^m a0 with a0 ≠ 0 and q not dividing a0. If q does not divide a take m = 0 and a0 = a. Otherwise write a = q c. Nonvanishing of a gives c ≠ 0, and natDegree a = d + natDegree c gives natDegree c < natDegree a. Apply induction to c and multiply its factorization by q. The cofactor remains nonzero and not divisible by q.
4. The exponent is unique. Given q^m a0 = q^n b0 with both cofactors not divisible by q, suppose m < n. Write n = m + k with k > 0, cancel the nonzero factor q^m, and obtain a0 = q^k b0. Since k > 0, this makes q divide a0, a contradiction. The case n < m gives the same contradiction for b0. Thus m = n. Define μ(a) for nonzero a to be this unique exponent, and put μ(0) = 0.
5. The factorizations 1 = q^0 · 1 and q = q^1 · 1 give μ(1) = 0 and μ(q) = 1 by uniqueness. For nonzero a,b, multiply their factorizations. Their cofactors have nonzero product, and step 2 shows q does not divide that product. Uniqueness gives μ(ab) = μ(a) + μ(b).
6. If μ(a) = 0 for nonzero a, its factorization identifies a with its q-free cofactor, so q does not divide a. Conversely, if q does not divide a, the factorization a = q^0 a and uniqueness give μ(a) = 0. Step 3 with the unique exponent supplies the asserted nonzero cofactor for every nonzero a. These statements are precisely all the required properties.

## Key steps

1. Irreducibility gives nonvanishing, positive degree, and noninvertibility of q.
2. Use a gcd and Bezout identity to prove that q divides a product only if it divides a factor.
3. Extract powers of q by strong induction on polynomial degree.
4. Cancel powers of q to establish uniqueness of the exponent and define μ.
5. Multiply factorizations to prove additivity and compute μ(1) and μ(q).
6. Characterize exponent zero and retain the nonzero cofactor factorization.

## Reference use

### local-project

Queries:
- `rg -n 'theorem.*(multiplicity_eq_zero|multiplicity_eq_iff|finiteMultiplicity|exists_eq_pow|multiplicity_one|multiplicity_self|multiplicity_mul)|def multiplicity'`
- `rg -n 'transcendental_iff_injective|theorem.*aeval_injective|finiteMultiplicity_iff|finiteMultiplicity.*not_isUnit|Irreducible.prime'`
- `rg -n 'namespace RationalFunctionField|def heightOneSpectrumOfIrreducible|class HasPrincipalDivisors'`
- `rg -n 'p06_9e0f5043ff_elp_integer_order|p06_9e0f5043ff_io_polynomial_exponent|p06_9e0f5043ff_io_fraction_extension'`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Multiplicity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project`

The snapshot pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Multiplicity.lean provides multiplicity_eq_zero, FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd, multiplicity_mul, and multiplicity_self; Algebraic/Basic.lean provides transcendental_iff_injective. These five declarations were checked transitively and use only propext, Classical.choice, and Quot.sound. Installed dependencies matched their pins and were clean. DivisorClassGroup.lean confirms the unchanged root definition of HasPrincipalDivisors. The helper-name search found no matches in the pinned project; proposed names also had no DAG collisions. Both proposed types elaborated after import Submission using the existing import-only interface. The full frozen Submission still fails on three pre-existing unknown attribute targets, so exact-source validation remains blocked; interface elaboration is not comparator acceptance.
