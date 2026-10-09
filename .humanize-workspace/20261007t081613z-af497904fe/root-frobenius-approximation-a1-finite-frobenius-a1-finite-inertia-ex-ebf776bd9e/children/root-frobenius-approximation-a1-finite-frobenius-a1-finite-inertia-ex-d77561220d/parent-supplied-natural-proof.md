# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1.minpoly_roots-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, α, and hα : IsIntegral ℤ α. Set f = minpoly ℤ α and g = minpoly ℚ α. The polynomial f is monic and its evaluation at α is zero. Also α is integral over ℚ because E is finite-dimensional over ℚ, so g is monic.
2. By minpoly.isIntegrallyClosed_eq_field_fractions' in Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean, g is the coefficient extension of f from ℤ to ℚ. Composing coefficient maps therefore identifies g extended to E with p = f.map (Int.castRingHom E). Normality, supplied by IsGalois ℚ E, gives that g splits over E by Normal.splits. Separability of E/ℚ gives that g is separable.
3. Apply Polynomial.exists_finset_of_splits from Mathlib/FieldTheory/Separable.lean to g and the rational coefficient map into E. It supplies a finite set s of elements of E such that p = C(g.leadingCoeff mapped to E) · ∏ b ∈ s, (X − C b). Since g is monic, the leading-coefficient factor is 1. Put n = s.card and choose a bijection from Fin n to the subtype of elements of s. Let β be its composition with the subtype inclusion into E. Both maps are injective, so β is injective. Reindexing the finite product gives p = ∏ i : Fin n, (X − C(β i)).
4. For each i, evaluate this factorization at β i. The factor indexed by i becomes zero, so p(β i) = 0. This is precisely the evaluation of the monic integer polynomial f at β i under the integer coefficient map. Thus f witnesses IsIntegral ℤ (β i).
5. Fix a rational algebra automorphism σ of E. Its underlying ring homomorphism fixes every integer. Applying it to the equation f(α) = 0 therefore gives p(σ α) = 0: this follows term by term because σ preserves finite sums, products, powers, and integer coefficients. Evaluating the factorization from step 3 now gives ∏ i : Fin n, (σ α − β i) = 0. In a field a finite product is zero only if one factor is zero. Hence there is i with σ α − β i = 0, equivalently β i = σ α. Together with steps 3 and 4, this proves every asserted conjunct.

## Key steps

1. Identify the integer minimal polynomial after coefficient extension to ℚ and E.
2. Use Galois normality and separability to obtain a finite set of distinct linear factors.
3. Enumerate that set by Fin n and reindex the factorization.
4. Use the monic integer polynomial to prove integrality of every listed root.
5. Apply each automorphism to the vanishing equation and extract a zero linear factor to cover its conjugate.

## Reference use

### local-project

Queries:
- `esymmAlgHom_surjective|coeff_eq_esymm_roots_of_splits|isIntegrallyClosed_eq_field_fractions|prod.*sub.*sq|exists.*discriminant`
- `def IsSymmetric|def esymmAlgHom|esymmAlgHom_X|isSymmetric_iff|def esymm`
- `def esymmAlgHom|theorem.*splits|lemma.*splits|roots.*nodup|nodup.*roots`
- `minpoly|esymm|discriminant|Vandermonde`
- `p09_af497904fe_irp_(minpoly_roots|squared_vandermonde_symmetric|integer_discriminant)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_GaloisRep_Adic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Normal/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Separable.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Polynomial/Vieta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/tmp/p09_irp_decomposition_q9zb6p3m/TypeChecks.lean`
- `/tmp/p09_irp_decomposition_q9zb6p3m/TypeChecks.lean.log`
- `/tmp/p09_irp_decomposition_q9zb6p3m/diagnostic.json`

The manifest pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The snapshot supplies minimal-polynomial coefficient extension, Normal.splits, Polynomial.exists_finset_of_splits, the symmetry predicate, elementary symmetric substitution sending variable i to e_(i+1), and Vieta's coefficient formula. The project definition module search found no relevant polynomial helper. The installed mathlib revision matches and its tracked files are clean. Transitive axiom checks for the six cited library lemmas reported only propext, Classical.choice, and Quot.sound. All three proposed types elaborate after import Submission using the policy-compliant disposable copy; polynomial multiplication instances were inspected. The diagnostic records the matching policy digest, omitted lines, reversible source/build hashes, and successful absence probes for all eight targets. Proposed names have no existing DAG reservation.
