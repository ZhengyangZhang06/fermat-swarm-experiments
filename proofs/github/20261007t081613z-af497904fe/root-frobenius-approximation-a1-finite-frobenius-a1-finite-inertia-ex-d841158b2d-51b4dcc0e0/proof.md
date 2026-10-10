# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1.squared_vandermonde_symmetric-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n. Let T be the finite set of pairs (i,j) in Fin n × Fin n with i < j, and let P = ∏ (i,j) ∈ T, (X_i − X_j)² in MvPolynomial (Fin n) ℤ. By the definition of MvPolynomial.IsSymmetric, it suffices to prove rename π P = P for every permutation π of Fin n.
2. Fix such a permutation. Define a map Bπ on T by sending (i,j) to the increasing ordering of (π(i),π(j)): use (π(i),π(j)) if π(i) < π(j), and otherwise use (π(j),π(i)). Since i < j implies i ≠ j and π is injective, the two image entries are distinct; totality of the order therefore makes the resulting pair an element of T.
3. The analogous construction B_(π⁻¹) is an inverse to Bπ. Indeed, sorting preserves the unordered pair of entries. Applying π⁻¹ to the unordered pair {π(i),π(j)} recovers {i,j}, whose unique increasing ordering is (i,j). The same argument with π and π⁻¹ exchanged proves the other inverse identity. Thus Bπ is a bijection of T.
4. For a pair (i,j) ∈ T, the polynomial (X_(π(i)) − X_(π(j)))² equals the factor indexed by Bπ(i,j). If the image entries are already increasing this is immediate. Otherwise their difference is the negative of the increasing-order difference, and (−z)² = z² in the commutative polynomial ring.
5. Renaming is a ring homomorphism sending X_i to X_(π(i)), so it carries P to the product over T of the polynomials in step 4. Replace each factor using that equality and reindex by the bijection Bπ from step 3. The result is exactly P. This argument also covers empty T, whose product is 1. Since π was arbitrary, P is symmetric.

## Key steps

1. Express symmetry as invariance under arbitrary variable renaming by a permutation.
2. Map each increasing pair to the sorted pair of its permuted entries.
3. Prove this map is bijective using the inverse permutation.
4. Show that reversing a difference does not change its square.
5. Commute renaming with the product and reindex by the pair bijection.

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
