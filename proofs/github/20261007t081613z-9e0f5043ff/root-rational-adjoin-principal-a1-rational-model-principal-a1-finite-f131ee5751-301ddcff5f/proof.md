# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put R = K[T] and e(a) = a(x). Transcendence makes e injective. Irreducibility gives q nonzero and not a unit. Its natural degree d is positive: otherwise q is a nonzero constant and therefore a unit. Also q does not divide 1. If q does not divide a, gcd(q,a) is a unit, since a nonunit divisor of the irreducible q is associated to q and would force q to divide a. Bezout in the Euclidean ring R gives u q + v a = 1. Multiplying this equality by b proves that q dividing ab and not dividing a implies q divides b. Thus q is prime.
2. For each nonzero a, induction on its natural degree gives a = q^m a0 with q not dividing a0. If q does not divide a, take m = 0 and a0 = a. Otherwise write a = q c. Both c and q are nonzero, so natDegree a = d + natDegree c; since d is positive, induction applies to c and yields the desired factorization with exponent increased by one. All remaining factors are nonzero. If q^m a0 = q^n b0 with both remaining factors not divisible by q and m < n, cancel the nonzero q^m to obtain a0 = q^(n-m) b0, contradicting q not dividing a0. The case n < m is symmetric. Hence the exponent is unique; denote it by μ(a).
3. If neither a0 nor b0 is divisible by q, primality shows their product is not divisible by q. Multiplying the factorizations of nonzero a and b and using uniqueness therefore gives μ(ab) = μ(a) + μ(b). The factorizations 1 = q^0 * 1 and q = q^1 * 1 give μ(1) = 0 and μ(q) = 1. For any nonzero a, μ(a) = 0 if and only if q does not divide a: a positive exponent supplies a factor q, while exponent zero has a = a0.
4. For each nonzero f choose the assumed representation f = e(a)/e(b) with b nonzero. Injectivity gives e(b) nonzero and the nonzero f forces a nonzero. Set ν(f) = μ(a) - μ(b) as an integer, and set ν(0) = 0. For a second representation e(c)/e(t) of the same nonzero f, both c and t are nonzero. Cross multiplication gives e(at) = e(cb), and injectivity gives at = cb. Applying step 3 gives μ(a) + μ(t) = μ(c) + μ(b), so the two integer differences agree. Thus the chosen definition has the asserted formula for every such representation.
5. Multiplying representations and applying step 3 gives ν(fg) = ν(f) + ν(g) for nonzero f,g. Inverting a nonzero fraction exchanges its nonzero numerator and denominator, giving ν(f⁻¹) = -ν(f). Since f/g = f g⁻¹, these equalities give ν(f/g) = ν(f) - ν(g). The representations e(q) = e(q)/e(1) and 1 = e(1)/e(1) give ν(e(q)) = 1 and ν(1) = 0; e(q) is nonzero by injectivity.
6. Suppose nonzero f has a representation e(a)/e(b) with q not dividing b. Then b and a are nonzero and μ(b) = 0, hence ν(f) = μ(a) is nonnegative.
7. Conversely suppose f is nonzero and ν(f) is nonnegative. Choose a nonzero-denominator representation and factor a = q^m a0 and b = q^n b0 using step 2. The numerator is nonzero, and ν(f) = m - n implies n ≤ m. Since e(q) and e(b0) are nonzero, cancellation of e(q)^n gives f = e(q^(m-n) a0)/e(b0). The denominator b0 is not divisible by q. This is the required representation. Steps 6 and 7 prove the equivalence, and together with steps 4 and 5 establish every asserted property of ν.

## Key steps

1. Prove q is prime and has positive degree.
2. Factor each nonzero polynomial uniquely as q^m times a factor not divisible by q.
3. Prove additivity of the exponents and compute the exponents of 1 and q.
4. Define the integer difference on nonzero fractions and prove representation independence by cross multiplication.
5. Derive the quotient law and the value at q(x).
6. Characterize nonnegative order by cancelling common powers of q.

## Reference use

### local-project

Queries:
- `structure Place|class Place|extends ValuationSubring|def Place`
- `exists.*[Pp]ow.*[Nn]ot|finiteMultiplicity|multiplicity_eq_zero|theorem multiplicity_mul`
- `aeval_injective|transcendental_iff`
- `class IsPrincipalIdealRing|structure IsPrincipal|class IsPrincipal`
- `principal.*valuation|valuation.*principal|IsPrincipalIdealRing.*ValuationSubring|exists.*ValuationSubring`
- `p06_9e0f5043ff_elp_(fraction_subalgebra|integer_order|principal_ideals_of_order)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Multiplicity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Span.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/Discrete/IsDiscreteValuationRing.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-04071bed87/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-04071bed87/decomposition-typecheck/Submission.frozen-source-check.log`

The snapshot records project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Place requires precisely a valuation subring, containment of constants, properness, and IsPrincipalIdealRing. The inspected library supplies evaluation injectivity from transcendence, finite-multiplicity factorization, multiplicity additivity, and the relevant ring structures. The constructor search in Valuation/Discrete/IsDiscreteValuationRing.lean returned no match; proposed-name searches also returned no collisions. All nine dependency revisions match their pins with clean tracked files, and inspected compiled-context sources match the snapshot. Library axiom checks report only propext, Classical.choice, and Quot.sound. All three proposed types elaborate after import Submission in the existing isolated import-only interface, and inherited multiplication checks pass by definitional equality. The unchanged authoritative Submission still fails on three pre-existing unknown attribute targets; successful authoritative import validation remains required before child activation. These checks are not comparator acceptance.
