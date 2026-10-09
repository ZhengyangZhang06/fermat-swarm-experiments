# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1.clear_first_column-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put p = B(0,0). For each i : Fin m, divisibility supplies a coefficient a(i) with B(i.succ,0) = p a(i). Since R is commutative, B(i.succ,0) = a(i)p as well. Choose these coefficients simultaneously.
2. Define a square matrix N using Matrix.of: its zeroth row is zero, and N(i.succ,j) equals a(i) if j = 0 and zero otherwise. Thus every column of N except column zero is zero, and N(0,j) = 0 for every j.
3. For arbitrary row s and column t, expand (N N)(s,t) as the sum over k of N(s,k)N(k,t). When k = 0 the second factor is zero; when k ≠ 0 the first factor is zero. Every summand vanishes, so N N = 0.
4. Set U = I - N and W = I + N, with I the matrix identity. Distributing matrix multiplication gives U W = I + N - N - N N = I and W U = I - N + N - N N = I. Consequently U, with inverse W, defines a unit of the matrix ring, so IsUnit U holds for matrix multiplication.
5. The multiplication formula gives (N B)(0,j) = 0 and (N B)(i.succ,j) = a(i)B(0,j), because only the summand with intermediate index zero can remain. Therefore (U B)(0,j) = B(0,j) and (U B)(i.succ,j) = B(i.succ,j) - a(i)B(0,j). Taking j = 0 yields (U B)(i.succ,0) = a(i)p - a(i)p = 0.
6. These identities and the unit from step 4 give every required conclusion. If m = 0, the coefficient family is empty, N is zero and U is the identity, so the same construction and all the assertions remain valid.

## Key steps

1. Choose coefficients expressing the lower entries of column zero as multiples of B(0,0).
2. Put these coefficients in column zero of a matrix N whose zeroth row vanishes.
3. Show N squared is zero by inspecting each multiplication summand.
4. Exhibit I + N as a two-sided inverse to U = I - N.
5. Compute UB to prove preservation of the first row and vanishing below the pivot.

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
