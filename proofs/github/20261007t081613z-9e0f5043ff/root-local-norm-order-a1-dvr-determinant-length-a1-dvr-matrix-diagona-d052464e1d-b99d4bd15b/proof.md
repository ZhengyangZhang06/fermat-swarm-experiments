# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1.clear_first_row-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put p = H(0,0). For each j : Fin m, choose b(j) with H(0,j.succ) = p b(j), using the assumed divisibility.
2. Define a square matrix M using Matrix.of by M(0,0) = 0, M(0,j.succ) = b(j), and M(i.succ,t) = 0 for every i : Fin m and t : Fin (m + 1). Column zero is zero, and every row other than row zero is zero.
3. In the sum expressing (M M)(s,t), the term with intermediate index k = 0 vanishes because M(s,0) = 0. Every term with k ≠ 0 vanishes because row k of M is zero. Thus M M = 0. Set V = I - M and W = I + M. Distributivity yields V W = I + M - M - M M = I and W V = I - M + M - M M = I. This gives a unit of the matrix ring with value V and inverse W, hence IsUnit V for matrix multiplication.
4. Since column zero of M is zero, (H M)(s,0) = 0. In column j.succ, only intermediate index zero contributes, so (H M)(s,j.succ) = H(s,0)b(j). Therefore (H V)(s,0) = H(s,0) and (H V)(s,j.succ) = H(s,j.succ) - H(s,0)b(j).
5. Step 4 gives (H V)(0,0) = p and, by the first hypothesis, (H V)(i.succ,0) = 0. For the top row it gives (H V)(0,j.succ) = p b(j) - p b(j) = 0. For the remaining block the first hypothesis gives (H V)(i.succ,j.succ) = H(i.succ,j.succ) - 0 b(j) = H(i.succ,j.succ).
6. Every index in Fin (m + 1) is either zero or a successor. The four cases in step 5 therefore prove, entry by entry, equality with the nested Fin.cases matrix in the conclusion. Together with the unit from step 3 this proves the assertion. For m = 0 the coefficient family is empty, M is zero, and the same identities apply without any nonvanishing assumption.

## Key steps

1. Choose coefficients for the off-pivot entries of row zero.
2. Place these coefficients in row zero of a matrix M with column zero vanishing.
3. Prove M squared is zero and obtain V = I - M as a matrix unit.
4. Compute right multiplication by V using the unique possible summand at intermediate index zero.
5. Use the zero first-column hypothesis to preserve the trailing block and identify all four Fin.cases entries.

## Reference use

### local-project

Queries:
- `rg -n 'pivot|transvection|hasPrincipalDivisors_of_transcendental' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project --glob '*.lean'`
- `rg -n 'divisible.*pivot|pivot.*divisible|clear_first_column|clear_first_row' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib --glob '*.lean'`
- `sed -n '1,140p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean`
- `sed -n '310,350p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean`
- `sed -n '1180,1236p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `rg -n 'p06_9e0f5043ff_sdp_clear_first_(column|row)' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/p06-sdp-decomposition-219xgs5a/CheckTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Fermat/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/Permutation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/README.txt`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/Submission.build.log`
- `/tmp/p06-sdp-decomposition-219xgs5a/CheckTypes.lean`
- `/tmp/p06-sdp-decomposition-219xgs5a/CheckTypes.log`

The manifest pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; the installed mathlib matches and has clean Git status. Transvection.lean supplies single-entry row/column operations, but its packaged pivot reduction uses a field and division. The targeted search for divisible-pivot and first-row/column clearing lemmas returned no matches. Mul.lean and Permutation.lean supply permutation multiplication infrastructure. Neither proposed identifier occurs in the inspected DAG or Submission. Both proposed types passed Lean 4.33.1 elaboration after import Submission in the run's existing import-only interface environment; expanded instance output confirms Matrix.semiring supplies the unit monoid, including for Matrix.of. This is an interface check: the complete frozen Submission has pre-existing unresolved attribute targets, so full-module validation remains outstanding. Axiom checks of Matrix.mul_apply, Matrix.one_submatrix_mul and Matrix.mul_submatrix_one reported only propext, Classical.choice and Quot.sound. No candidate theorem or comparator acceptance is claimed.
