# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1.integer_discriminant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, f, n, and β satisfying the hypotheses, and write ι : ℤ → K for the integer coefficient homomorphism. In MvPolynomial (Fin n) ℤ put P = ∏ (i,j) with i < j, (X_i − X_j)². The sibling theorem p09_af497904fe_irp_squared_vandermonde_symmetric proves that P is symmetric.
2. Apply MvPolynomial.esymmAlgHom_surjective from Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean with coefficient ring ℤ, variable set Fin n, and n generators. Its cardinality hypothesis holds because Fintype.card (Fin n) = n. Consequently there exists Q ∈ MvPolynomial (Fin n) ℤ such that P is obtained from Q by substituting e_(i.val+1) for variable i, where e_k is the kth elementary symmetric polynomial. This indexing is the defining substitution of esymmAlgHom.
3. For 1 ≤ k ≤ n, let E_k be e_k evaluated at β with coefficients mapped by ι. By the definition of e_k, E_k is the sum, over all k-element subsets of Fin n, of the corresponding products of β-values. Expanding the assumed factorization of f over K, the coefficient of X^(n−k) is obtained by selecting the constant term from exactly k linear factors and X from all others. It is therefore (−1)^k E_k. The same coefficient on the left is ι(f.coeff (n−k)). Thus ι(f.coeff (n−k)) = (−1)^k E_k. This finite expansion is also the identity Multiset.prod_X_sub_C_coeff in Mathlib/RingTheory/Polynomial/Vieta.lean, applied to the multiset of the n indexed β-values.
4. The square of (−1)^k is 1. Multiplying the equality in step 3 by (−1)^k yields E_k = ι((−1)^k · f.coeff (n−k)). For i : Fin n, define the integer c_i = (−1)^(i.val+1) · f.coeff (n−(i.val+1)). Since i.val < n, the integer k = i.val+1 lies between 1 and n, so step 3 applies and gives E_(i.val+1) = ι(c_i).
5. Define D ∈ ℤ by evaluating Q at the integer family c. Polynomial evaluation is a finite sum of coefficient-weighted monomials. Since ι preserves finite sums, products, and powers, ι(D) is the evaluation of Q over K at the family ι(c_i). By step 4 this family is precisely the evaluated elementary symmetric generators. Evaluating the substitution identity of step 2 at β therefore gives ι(D) = P(β) = ∏ (i,j) with i < j, (β i − β j)². This is the exact filtered-finset product in the conclusion.
6. For every indexed pair i < j, we have i ≠ j; injectivity of β gives β i ≠ β j. Hence β i − β j and its square are nonzero in K. Their finite product is nonzero because K is a field. This includes an empty indexing set, whose product is 1. Step 5 implies ι(D) ≠ 0. If D were zero, its image would be zero, a contradiction. Thus D ≠ 0, proving both required properties. When n = 0 the family c and all generator conditions are empty, and the same evaluation and empty-product arguments apply without alteration.

## Key steps

1. Use squared Vandermonde symmetry and elementary symmetric surjectivity to express P as Q(e₁,…,eₙ) over ℤ.
2. Compare coefficients in the assumed linear factorization to express each elementary symmetric value as a cast of a signed integer coefficient.
3. Evaluate Q at those signed integer coefficients to define D.
4. Commute integer coefficient extension with evaluation to identify the image of D with the required filtered product.
5. Use injectivity of β and nonvanishing of finite products in a field to prove D ≠ 0.

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
