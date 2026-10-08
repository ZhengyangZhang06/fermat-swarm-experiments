# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1.fraction_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Set e = Polynomial.aeval x. Transcendence means that e is injective, so e(a) ≠ 0 exactly when a ≠ 0. For any nonzero f choose a representation f = e(a)/e(b) with b ≠ 0. Its numerator a is nonzero, because a = 0 would give f = 0.
2. Suppose e(a)/e(b) = e(c)/e(t), where all four polynomials are nonzero. The denominators evaluate to nonzero elements, so cross multiplication gives e(a t) = e(c b). Injectivity gives a t = c b. The assumed product rule yields μ(a) + μ(t) = μ(c) + μ(b). Casting this equality into the integers and rearranging proves μ(a) - μ(b) = μ(c) - μ(t), with all differences taken in the integers.
3. Define ν(0) = 0. For each nonzero f use a chosen representation from step 1 and define ν(f) = (μ(a) : ℤ) - (μ(b) : ℤ). Step 2 makes this independent of the choice. In particular, for every nonzero a,b, their evaluated quotient is nonzero, and comparison with its chosen representation proves the required formula for ν(e(a)/e(b)).
4. Let f,g be nonzero, and choose f = e(a)/e(b) and g = e(c)/e(t) with all four polynomials nonzero as in step 1. Field arithmetic and the fact that e respects multiplication give f/g = e(a t)/e(b c). The polynomials a t and b c are nonzero because K[T] is a domain.
5. Apply the formula from step 3 and the product rule for μ to obtain ν(f/g) = (μ(a) : ℤ) + (μ(t) : ℤ) - ((μ(b) : ℤ) + (μ(c) : ℤ)) = ((μ(a) : ℤ) - (μ(b) : ℤ)) - ((μ(c) : ℤ) - (μ(t) : ℤ)) = ν(f) - ν(g). Along with the definition at zero and step 3, this proves the whole conclusion.

## Key steps

1. Use transcendence to obtain injective evaluation and nonzero numerators and denominators.
2. Cross-multiply equal fractions and apply additivity of μ to prove independence of the integer difference.
3. Define ν by chosen representations, with ν(0)=0, and establish its formula for every nonzero polynomial fraction.
4. Represent division using the polynomial products a t and b c.
5. Apply additivity and integer arithmetic to prove the division law.

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
