# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K and put M = Frac(K[T]), with t the image of T. The fraction-ring embedding is injective, evaluation at t equals that embedding, and t is nonzero and transcendental over K. Put s = t⁻¹, so s ≠ 0 and t = s⁻¹.
2. The element s is transcendental. Indeed, for any nonzero polynomial p of degree d, define p*(T) = Σ_{i=0}^d p_i T^(d−i). Its constant coefficient is the nonzero leading coefficient p_d, so p* is nonzero. Direct expansion gives t^d p(s) = p*(t). The right side is nonzero by transcendence of t. Therefore p(s) ≠ 0 for every nonzero p.
3. Every element of M is a fraction of polynomials in s. Zero is 0/1. For a nonzero element choose a(t)/b(t) with a,b nonzero, and let d = deg a and e = deg b. Let A and B be their reversed polynomials as in step 2. Expansion gives a(t) = s^(−d)A(s) and b(t) = s^(−e)B(s), so the quotient is s^(e−d)A(s)/B(s). If e ≥ d, absorb s^(e−d) into the numerator polynomial; otherwise absorb s^(d−e) into the denominator polynomial. The resulting denominator is nonzero, since B is nonzero, evaluation at s is injective, and s ≠ 0.
4. Apply finite_place_model to the fields K,M, the generator s, and q = T. This polynomial is monic and irreducible: its degree is one, so any factorization into nonzero polynomials has a degree-zero, hence unit, factor. Obtain a place v whose valuation subring B₀ consists exactly of fractions a(s)/b(s) with T not dividing b. The child gives v.deg = 1, v.ord(s) = 1, and v.ord(c(s)) = 0 whenever T does not divide c.
5. The element t does not belong to B₀. Otherwise t = a(s)/b(s) with T not dividing b. Multiplication by s and the nonzero b(s) gives b(s) = s a(s). Injectivity of evaluation at s implies b = Ta, contradicting the permitted denominator condition.
6. Let a be a nonzero polynomial of degree d, and let A be its reversed polynomial. Its constant coefficient is the nonzero leading coefficient of a, so T does not divide A. Thus v.ord(A(s)) = 0 by step 4. Both factors in a(t) = s^(−d)A(s) are nonzero. Using Place.ord_mul and Place.ord_zpow together with v.ord(s) = 1 gives v.ord(a(t)) = −d, interpreted as an integer.
7. To prove uniqueness, let w be any project place with t absent from W = w.toValuationSubring. The valuation property puts s in W. It is a nonunit there, since its inverse is t. Evaluation at s therefore maps K[T] into W, and the contraction J of W's maximal ideal is a proper ideal containing T. The ideal (T) is maximal because evaluation at zero identifies K[T]/(T) with K. Hence J = (T). Every b not divisible by T consequently evaluates to a W-unit. The fraction characterization from step 4 then gives B₀ ⊆ W.
8. Conversely, take nonzero f ∈ W and use step 3 to express f = a(s)/b(s) with a,b nonzero. Repeatedly remove factors T to obtain a = T^r a₀ and b = T^k b₀ with T dividing neither remaining polynomial. By step 7, u = a₀(s)/b₀(s) is a W-unit, and f = u s^(r−k). If r < k, the product f u⁻¹ s^(k−r−1) equals s⁻¹ = t and belongs to W, a contradiction. Thus r ≥ k, and f = (T^(r−k)a₀)(s)/b₀(s) belongs to B₀ by step 4. Zero also belongs to B₀, so W ⊆ B₀. Equality of the valuation subrings and Place.ext give w = v. Steps 4–6 and this uniqueness statement prove the required conjunction.

## Key steps

1. Prove that s = t⁻¹ is transcendental using reversed polynomials.
2. Express every rational function as a polynomial fraction in s.
3. Apply finite_place_model at the irreducible polynomial T to construct infinity with degree one.
4. Use injectivity of evaluation to show that its valuation subring excludes t.
5. Reverse each nonzero polynomial to compute its order as minus its degree.
6. For any other place excluding t, contract its maximal ideal to (T) in K[s].
7. Exclude negative powers of s and identify the valuation subrings, then apply Place.ext.

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
