# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put R = K[T], e(a) = a(x), and A = v.toValuationSubring. Evaluation e is injective. The irreducible polynomial q is nonzero and not a unit, so q does not divide 1. It is prime: if q does not divide a, the greatest common divisor of q and a is a unit, and the Euclidean algorithm gives u q + t a = 1; multiplying by b proves that q dividing ab forces q to divide b. The membership hypothesis with denominator 1 shows e(a) ∈ A for every polynomial a.
2. Suppose q does not divide a. Then a ≠ 0, and therefore e(a) ≠ 0. The permitted fraction e(1)/e(a) belongs to A by the membership hypothesis. It is the inverse of e(a) in F, and both inverse identities hold in the subring A. Thus e(a), regarded as an element of A, is a unit.
3. Let π be e(q) regarded as an element of A. It is nonzero. It cannot be a unit: if it were, e(q)⁻¹ would belong to A and hence equal e(a)/e(b) with q not dividing b. Here b ≠ 0, so cross multiplication gives e(b) = e(q a). Injectivity implies b = q a, contradicting the denominator condition. Thus π is a nonunit.
4. To prove π irreducible, suppose π = yz in A. Both y and z are nonzero. Choose representations y = e(a)/e(b) and z = e(c)/e(t) with q dividing neither b nor t. Both denominator evaluations are nonzero. Cross multiplication and injectivity give ac = qbt in R. If q divided both a and c, write a = q a₁ and c = q c₁. Cancelling the nonzero factor q would yield q a₁c₁ = bt. Primality would then force q to divide b or t, a contradiction. Therefore q does not divide a or q does not divide c. In the first case, y⁻¹ = e(b)/e(a) belongs to A by the membership criterion, so y is a unit. In the second case, z⁻¹ = e(t)/e(c) belongs to A, so z is a unit. Together with step 3, this proves Irreducible π.
5. Apply the project's Place.ord_coe_irreducible to π to obtain v.ord(e(q)) = 1. For each a not divisible by q, choose the unit of A supplied in step 2 and apply Place.ord_coe_unit. Its image in F is e(a), so v.ord(e(a)) = 0. These are exactly the two conclusions.

## Key steps

1. Establish injective evaluation, primality of q, and membership of all polynomial evaluations.
2. Construct an inverse in the valuation subring for every polynomial not divisible by q.
3. Show q(x) is a nonunit by excluding its inverse through cross multiplication.
4. Prove q(x) irreducible by ruling out two q-divisible factor numerators.
5. Apply the project's irreducible and unit order formulas.

## Reference use

### local-project

Queries:
- `structure Place|def deg|def ord|ord_coe_unit|ord.*uniformizer|ord.*irreducible|hasPrincipalDivisors_of_transcendental|finite.*[Pp]lace|placeOfIrreducible|ResidueField|heightOneSpectrumOfIrreducible`
- `placeOfIrreducible|heightOneSpectrumOfIrreducible|residue.*[Aa]dj|finrank.*[Aa]djoinRoot|IsLocalization.*AtPrime|exists.*pow.*dvd`
- `finrank|basis|quotient|Quotient`
- `exists.*pow.*dvd|pow.*not_dvd|multiplicity.*finite|FiniteMultiplicity`
- `residue_eq_zero_iff|mem_maximalIdeal|surjective`
- `theorem.*prime|irreducible_iff_prime`
- `p06_9e0f5043ff_fpm_(exists_local_place|normalized_orders|residue_degree)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Multiplicity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/AdjoinRoot.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/PrincipalIdealDomain.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-ff0d532bf4/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-ff0d532bf4/decomposition-typecheck/InspectLibrary.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-ff0d532bf4/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-ff0d532bf4/decomposition-typecheck/Submission.frozen-source-check.log`

The snapshot pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Place requires a proper valuation subring containing K and an IsPrincipalIdealRing proof; its degree is the canonical residue-field finrank. Place.ord_coe_irreducible and Place.ord_coe_unit provide the required normalization. Multiplicity.lean supplies finite prime-power factorization and multiplicity additivity; AdjoinRoot.lean supplies finrank_quotient_span_eq_natDegree; ResidueField/Basic.lean identifies the residue kernel and supplies surjectivity. The targeted P2M search found no matching finite-place construction. Proposed names have no active-DAG or searched-source collisions. All nine installed dependencies match their pinned revisions and have clean tracked files. Audited supporting declarations depend only on propext, Classical.choice and Quot.sound. All proposed types elaborate against the existing isolated import-only Submission interface, whose project definitions match the snapshot byte-for-byte; definitional-equality checks verify the intended subring and residue-field algebra structures. The unchanged actual Submission still fails on three pre-existing unknown attribute targets, so actual import validation remains outstanding. These checks are not comparator acceptance.
