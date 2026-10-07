# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_classification-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, M, t and v as stated, and put V = v.toValuationSubring. The canonical map K[T] → M is injective. Because V contains K and t, it contains the image of every polynomial. Thus this map factors through a ring homomorphism K[T] → V.
2. Contract the maximal ideal of the local ring V along that homomorphism, obtaining an ideal p of K[T]. It is proper because one does not belong to the maximal ideal, and prime because the maximal ideal is prime.
3. The ideal p is nonzero. Otherwise every nonzero polynomial would map outside the maximal ideal of V and therefore to a unit of V. Every element of M is a polynomial fraction with nonzero denominator, so every element of M would then belong to V. This contradicts the properness field of the project place.
4. Choose a nonzero element q₀ of p with least degree. Dividing any element of p by q₀ gives a remainder still in p with smaller degree; minimality forces that remainder to be zero. Therefore p = (q₀). Multiplying q₀ by the inverse of its leading coefficient gives a monic generator q. This generator is nonzero and is not a unit since p is proper. It is irreducible: if q = ab, primality of p puts a or b in (q). If a = qc, cancellation of the nonzero q in q = qcb gives cb = 1, so b is a unit; the other case is symmetric.
5. If q does not divide b, then b does not belong to p. Consequently b(t) is a unit of V. Since a(t) belongs to V for every polynomial a, every fraction a(t)/b(t) with q not dividing b belongs to V. This proves one direction of the required characterization.
6. For the converse, zero has the permitted representation 0/1. Let f ∈ V be nonzero and write f = a(t)/b(t) with a,b nonzero. Repeated division by the positive-degree polynomial q terminates, giving a = q^r a₀ and b = q^s b₀, with q dividing neither a₀ nor b₀. By step 5, both a₀(t) and b₀(t) are units of V. Hence u = a₀(t)/b₀(t) is a V-unit and f = u q(t)^(r−s), with the exponent interpreted in ℤ.
7. The element q(t) belongs to the maximal ideal of V by the definition of p. If r < s, then f u⁻¹ q(t)^(s−r−1) = q(t)⁻¹ belongs to V. This would make q(t) a unit, contradicting its membership in the maximal ideal. Thus r ≥ s. The expression f = (q^(r−s)a₀)(t)/b₀(t) now has a denominator not divisible by q. This proves the reverse implication for every f. The monicity and irreducibility established in step 4 complete the statement.

## Key steps

1. Embed K[T] into the valuation subring using membership of t.
2. Contract the maximal ideal and prove that the contraction is proper, prime, and nonzero.
3. Use least-degree division and monic normalization to obtain an irreducible generator q.
4. Show that denominators not divisible by q become units.
5. Factor powers of q from a fraction and exclude a negative exponent using the maximal ideal.
6. Deduce the exact localization membership characterization.

## Reference use

### local-project

Queries:
- `HasPrincipalDivisors|namespace RationalFunctionField|structure Place|def ord|def deg|ord_unit_smul_zpow|placeOf|infinity`
- `namespace RationalFunctionField|heightOneSpectrumOfIrreducible|deg_placeOfPoint`
- `eq_of_le|eq_or_eq_top|overring|isUnit_iff|natDegree.*factor|sum.*natDegree|natDegree.*sum|multiplicity`
- `p06_9e0f5043ff_rmp_finite_place_model|p06_9e0f5043ff_rmp_finite_place_classification|p06_9e0f5043ff_rmp_infinity_place`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Polynomial/UniqueFactorization.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/FieldTheory/RatFunc/AsPolynomial.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1/decomposition-typecheck/Submission.frozen-source-check.log`

The DAG identifies the supplied statement as the depth-2 rational_model_principal child; the frozen root remains unchanged. DivisorClassGroup supplies Place, its DVR instance, normalized-order formulas, residue-field degree, degree_single, and HasPrincipalDivisors.exists_divisor. Mathlib supplies polynomial unique factorization and the proper-overring theorem ValuationSubring.eq_of_le_of_ne_top. Searches for the named RationalFunctionField constructions found only attribute references in specification files, not reusable construction definitions. Proposed names have no active-DAG or searched-source collisions. Both snapshot revisions and all nine dependencies match their manifests and have clean tracked files. Relevant project sources match the cached interface byte-for-byte. All three proposed types elaborate without warnings against the isolated import-only Submission interface. Definitional checks verify the canonical K-algebra through Polynomial.C and the residue-field algebra underlying Place.deg. Audited supporting declarations use only propext, Classical.choice, and Quot.sound. However, a fresh check of actual Submission.lean fails on three pre-existing unknown attribute targets: AlgebraicCurve.IsCurveOver.instNontrivialKaehler, AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply, and AlgebraicCurve.SemilinearAut.coe_torsion_smul. Actual import Submission validation remains an activation blocker; no comparator acceptance is claimed.
