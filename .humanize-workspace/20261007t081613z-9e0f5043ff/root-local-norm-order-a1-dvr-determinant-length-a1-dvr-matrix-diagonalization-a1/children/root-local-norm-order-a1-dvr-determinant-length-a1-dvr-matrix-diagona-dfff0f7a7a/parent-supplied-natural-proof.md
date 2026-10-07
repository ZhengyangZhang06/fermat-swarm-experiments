# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data and put p = D(r,c). Let σ swap 0 and r, and let τ swap 0 and c, on Fin (m + 1). Define permutation matrices S and T by S(i,j) = 1 when j = σ(i), and zero otherwise, and T(i,j) = 1 when i = τ(j), and zero otherwise. The matrix multiplication formula and σ² = τ² = identity give S² = T² = I. Thus S and T are invertible, each with itself as inverse. Set B = S D T. Multiplication gives B(i,j) = D(σ(i),τ(j)); hence B(0,0) = p and p divides every entry of B.
2. For each i : Fin m, choose α(i) with B(i.succ,0) = α(i)p. Such a choice follows from divisibility and commutativity. For each j : Fin m, choose β(j) with B(0,j.succ) = pβ(j). These choices also make sense when m = 0, since the indexing types are then empty.
3. Define N by N(i.succ,0) = α(i), with all its other entries zero. Define M by M(0,j.succ) = β(j), with all its other entries zero. Both satisfy N² = 0 and M² = 0. Indeed, in each summand N(i,k)N(k,j), the first factor is zero unless k = 0, and when k = 0 the second factor is zero. In each summand M(i,k)M(k,j), the second factor is zero unless k = 0, and when k = 0 the first factor is zero. Set U = I - N and V = I - M. Distributivity now gives U(I + N) = (I + N)U = I and V(I + M) = (I + M)V = I. These are two-sided matrix inverses.
4. Set H = U B. Its entries satisfy H(0,j) = B(0,j) and H(i.succ,j) = B(i.succ,j) - α(i)B(0,j). Therefore H(0,0) = p and H(i.succ,0) = α(i)p - α(i)p = 0. Define C(i,j) = H(i.succ,j.succ).
5. Set Z = H V. Because column zero of M is zero, Z(i,0) = H(i,0). For each j : Fin m, multiplication gives Z(i,j.succ) = H(i,j.succ) - H(i,0)β(j). Thus Z(0,j.succ) = pβ(j) - pβ(j) = 0, while Z(i.succ,j.succ) = H(i.succ,j.succ) = C(i,j). Also Z(0,0) = p and Z(i.succ,0) = 0. These four entry formulas identify Z with the matrix expressed by the nested Fin.cases in the conclusion.
6. Take P = U S and Q = T V. Their two-sided inverses are S(I + N) and (I + M)T, respectively, by the inverse identities from steps 1 and 3. Hence IsUnit P and IsUnit Q hold for matrix multiplication. Finally, associativity gives P D Q = U(S D T)V = U B V = H V = Z. Together with the entry formulas and the chosen C, this proves the exact conclusion.

## Key steps

1. Move the specified pivot to (0,0) using self-inverse permutation matrices.
2. Choose coefficients expressing the first-column and first-row entries as multiples of the pivot.
3. Construct square-zero matrices N and M, giving explicit inverse pairs I − N, I + N and I − M, I + M.
4. Left multiplication clears the first column below the pivot.
5. Right multiplication clears the first row and preserves the lower-right block.
6. Compose the operations, exhibit two-sided inverses, and verify the four cases of the resulting block matrix.

## Reference use

### local-project

Queries:
- `exists_irreducible|eq_unit_mul_pow_irreducible|exists.*pow.*[Ii]rreducible|eq_unit_mul_pow`
- `transvection_mul|mul_transvection|isUnit_transvection|det_fromBlocks|det_fin_succ|fromBlocks.*mul|mul_fromBlocks`
- `smithNormalForm|smith_normal_form|matrix_diagonalization|dividing_pivot|pivot_block`
- `def of|abbrev of|instance.*[Mm]onoid|instance.*[Rr]ing|instMul|protected def mul`
- `p06_9e0f5043ff_dmd_finite_family_dividing_member|p06_9e0f5043ff_dmd_split_divisible_pivot`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/FreeModule/PID.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/README.txt`
- `/tmp/p06-dmd-decomposition-9e0f5043ff/CheckTypes.interface-check.log`
- `/tmp/p06-dmd-decomposition-9e0f5043ff/AuditReferences.log`

The snapshot pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. DVR Basic supplies exists_irreducible and eq_unit_mul_pow_irreducible; PlacesOverDVR uses both. Matrix sources provide elementary-operation identities, block determinants, and the matrix multiplication instances. FreeModule/PID contains an abstract basis Smith-normal-form theorem. The project search found no matches for smithNormalForm, smith_normal_form, matrix_diagonalization, dividing_pivot, or pivot_block. Installed dependency revisions match their pins and have clean tracked trees; the four directly checked mathlib source files match the snapshot byte-for-byte. Axiom audits of the referenced DVR and matrix lemmas report only propext, Classical.choice, and Quot.sound. Both proposed names are absent from the searched DAG metadata and imported environment. Both exact type expressions pass the available import Submission interface check, and explicit instance output confirms matrix multiplication and the monoid from Matrix.semiring. Limitation: that existing Submission cache is an import-only shim; its README records pre-existing unknown attribute targets blocking the complete frozen Submission build. These checks therefore do not establish exact-source build or comparator acceptance.
