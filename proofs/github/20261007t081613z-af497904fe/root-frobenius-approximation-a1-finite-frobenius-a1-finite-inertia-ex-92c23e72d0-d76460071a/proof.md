# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.valuation_product_separation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, n, β, D, the integrality and product hypotheses, and an allowed prime ℓ and valuation subring V. Let m be the maximal ideal of the local ring V. Every integer cast belongs to V because V is a subring. For an element of V, its image in K belongs to V.nonunits exactly when that element belongs to m; this is ValuationSubring.coe_mem_nonunits_iff.
2. We first prove that every x ∈ K integral over ℤ belongs to V. Suppose instead that x ∉ V. Since 0 ∈ V, x ≠ 0. The valuation-subring property gives t = x⁻¹ ∈ V. The element t is not a unit of V: a V-inverse s would satisfy ts = 1 in K, forcing s = x and hence x ∈ V. Thus t ∈ m.
3. Choose a monic integer polynomial witnessing integrality of x, and write its equation as x^r + ∑_{k<r} a_k x^k = 0. Its degree r is positive, because a monic degree-zero polynomial is 1 and cannot vanish in a field. Multiply the equation in K by x^(−r), obtaining 1 + ∑_{k<r} a_k t^(r−k) = 0. All terms now belong to V, so injectivity of V → K makes this an equality in V. Each exponent r−k is positive, so t ∈ m implies t^(r−k) ∈ m. Multiplication by the integer coefficient preserves membership in m, as do finite sums and negation. The equation therefore implies 1 ∈ m, contradicting properness of m. This proves the containment claim, and applying it to each β i gives the first conclusion.
4. Since ℓ is prime and does not divide D.natAbs, the integers D and ℓ are relatively prime. Indeed, the positive gcd of D.natAbs and ℓ divides the prime ℓ, so it is either 1 or ℓ; the latter is excluded by nondivisibility. Integer Bézout gives u,v ∈ ℤ with uD + vℓ = 1. The hypothesis V.LiesOverPrime ℓ and step 1 put the element (ℓ : V) in m. If (D : V) also belonged to m, the Bézout identity, mapped into V, would put 1 in m. Hence (D : V) is outside m and is a unit of V.
5. Lift every β i to b_i ∈ V using step 3. The inclusion V → K preserves integer casts, subtraction, powers, and finite products. Its injectivity therefore lifts the assumed product equality to (D : V) = ∏_{i<j}(b_i − b_j)² in V. Every factor in this product belongs to V.
6. Fix i,j and suppose β i − β j ∈ V.nonunits. If i = j, the desired equality follows immediately. Otherwise, let a be the smaller of i,j and b the larger. By step 1, b_i − b_j belongs to m. The ordered difference b_a − b_b is either this element or its negative, so its square belongs to m. The pair (a,b) occurs in the filtered product of step 5. Factoring out its squared difference expresses that product as an element of m times a product of elements of V; ideal closure puts the whole product in m. This says (D : V) ∈ m, contradicting step 4. The unequal-index case is impossible, and therefore β i = β j. Together with step 3 this proves both conclusions for the arbitrary permitted ℓ and V, hence uniformly for all of them.

## Key steps

1. Identify ambient valuation nonunits with membership in the maximal ideal of V.
2. For an integral element outside V, put its inverse in the maximal ideal.
3. Divide a monic integral equation by its leading power to derive the contradiction 1 ∈ m.
4. Apply integer Bézout and LiesOverPrime to show that D is a unit of V.
5. Lift the integer product equality from K to V.
6. A nonunit difference at unequal indices forces a squared factor, and thus D, into the maximal ideal.

## Reference use

### local-project

Queries:
- `rg -n --glob '*.lean' 'LiesOverPrime|esymmAlgHom_surjective|isIntegrallyClosed_eq_field_fractions\x27|mem_of_isIntegral|isIntegral.*mem' project mathlib/Mathlib/RingTheory/Valuation mathlib/Mathlib/RingTheory/IntegralClosure mathlib/Mathlib/RingTheory/MvPolynomial mathlib/Mathlib/FieldTheory/Minpoly`
- `rg -n 'esymm.*coeff|coeff.*esymm|vieta' mathlib/Mathlib -g '*.lean'`
- `rg -n 'nodup_roots|separable_map|theorem separable|minpoly.*separable' mathlib/Mathlib/FieldTheory/Separable.lean mathlib/Mathlib/FieldTheory/Perfect.lean`
- `rg -n --glob '*.lean' 'integer_root_product|valuation_product_separation|conjugate_separation' project/Definitions project/Theorems project/Submission.lean`
- `sed -n '551,626p' mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `python3 .humanize/cs-split-diagnostic-p625iw0i/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Separable.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Polynomial/Vieta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/cs-split-diagnostic-p625iw0i/report.json`

Search commands using project/ and mathlib/ were run from the specified snapshot root. The snapshot confirms the minimal-polynomial compatibility theorem, separability and distinct-root APIs, MvPolynomial.esymmAlgHom_surjective with generators indexed by i+1, Vieta identities, and the bridge from ambient valuation nonunits to the maximal ideal. LiesOverPrime is exactly membership of the natural-number cast in ambient nonunits. The proposed-helper-name search returned no matches in the searched pinned project files. Project revision 20574e45daf714e745af8e649c7b61b21eed5644, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and pinned dependencies were checked clean. Both proposed types elaborated after import Submission at proof-base commit 0e4c21ecef38655f90fdf89c00e55ba35d7e9369 using a disposable policy-compliant compiler copy. Integer casts, valuation-subring multiplication, and the ambient-nonunit interpretation were checked. Audited library declarations depend only on propext, Classical.choice, and Quot.sound. The diagnostic receipt records the matching policy digest, exact omitted lines 10 and 11, reversible original/build hashes, and a successful Lean absence probe for all eight omitted targets. Protected files remained unchanged. These are interface diagnostics, not comparator proof acceptance.
