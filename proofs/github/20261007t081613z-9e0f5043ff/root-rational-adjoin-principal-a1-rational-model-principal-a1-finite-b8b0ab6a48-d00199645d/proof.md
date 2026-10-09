# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.residue_degree-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put R = K[T], e(a) = a(x), A = v.toValuationSubring, and κ = v.ResidueField, with their canonical K-algebra structures. Evaluation e is injective. Irreducibility gives q ≠ 0 and says q is not a unit, so q does not divide 1. The membership hypothesis with denominator 1 puts every e(a) in A. If q does not divide a, then a and e(a) are nonzero, and the permitted fraction e(1)/e(a) belongs to A. Consequently e(a) is a unit of A.
2. The element e(q) is a nonunit of A. Otherwise its inverse would belong to A and have a representation e(a)/e(b) with q not dividing b. Cross multiplication, using e(q) ≠ 0 and e(b) ≠ 0, would give e(b) = e(q a), and injectivity would imply q divides b, a contradiction. Since A is local, e(q) belongs to its maximal ideal and has zero residue.
3. Compose the K-algebra evaluation map R → A with the canonical residue map A → κ to obtain a K-algebra homomorphism φ. If q divides a, then e(a) is an A-multiple of e(q), so φ(a) = 0. If q does not divide a, step 1 makes e(a) a unit; its image under the residue homomorphism is a unit in the nontrivial field κ and hence is nonzero. Therefore φ(a) = 0 if and only if q divides a. Its kernel is exactly the principal ideal (q).
4. The map φ is surjective. Indeed, given r ∈ κ, choose h ∈ A with residue r, using surjectivity of the residue quotient map. Represent h = e(a)/e(b) with q not dividing b. The greatest common divisor of q and b is a unit, since a nonunit common divisor would be associated to the irreducible q and would force q to divide b. The Euclidean algorithm thus gives u q + t b = 1. Applying φ and using φ(q) = 0 gives φ(t)φ(b) = 1. The identity h e(b) = e(a) in A gives r φ(b) = φ(a). Multiplying by φ(t) yields r = φ(a t), proving surjectivity.
5. Since φ is a surjective K-algebra homomorphism with kernel (q), it induces a K-algebra isomorphism R/(q) → κ. Explicitly, the induced map sends the class of a to φ(a); the kernel calculation makes it well-defined and injective, and step 4 makes it surjective. Thus κ and R/(q) have equal K-dimension.
6. Let d = q.natDegree. This number is positive because q is nonzero and a degree-zero polynomial over K would be a unit. Division by the monic polynomial q writes every a as q s + t, where t is zero or has degree less than d. Therefore the residue classes of 1,T,…,T^(d−1) span R/(q). For independence, a linear relation among these classes gives a polynomial p = Σ_{i<d} cᵢ T^i whose class is zero, so q divides p. If p were nonzero, writing p = q s would give s ≠ 0 and natDegree p = d + natDegree s ≥ d. This contradicts the degree bound for p. Hence p = 0, and comparing coefficients gives every cᵢ = 0. The displayed classes form a basis indexed by Fin d.
7. It follows that Module.finrank K (R/(q)) = d, and step 5 transfers this equality to κ. By the project's definition v.deg = Module.finrank K v.ResidueField, we conclude v.deg = q.natDegree.

## Key steps

1. Embed polynomial evaluations in the valuation subring and identify the evaluations prime to q as units.
2. Show q(x) has zero residue by proving it is a nonunit.
3. Construct the polynomial-to-residue algebra map and identify its kernel as (q).
4. Use Bézout inverses for permitted denominators to prove surjectivity.
5. Identify the residue field with K[T]/(q) as a K-algebra.
6. Prove the degree-bounded monomial classes form a basis.
7. Transfer finrank and unfold the project's definition of place degree.

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
