# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix A. Choose an irreducible uniformizer π using IsDiscreteValuationRing.exists_irreducible. The pinned factorization theorem says that every nonzero x ∈ A can be written x = uπ^e with u ∈ Aˣ and e ∈ ℕ. If p = uπ^a and x = wπ^b with a ≤ b, then x = p(u⁻¹wπ^(b-a)). Thus p divides x. It also divides zero.

2. We prove the assertion by induction on m. For m = 0, take P and Q to be identity matrices and d to be the unique function on Fin 0. Both matrices are units. All matrices of this empty shape are equal, so the required matrix identity holds, and the nonzero-entry assertion is vacuous.

3. Suppose the assertion holds for m and let D have size m+1 with nonzero determinant. Some entry of D is nonzero: otherwise D is the zero matrix of positive size and has zero determinant. Factor each of its finitely many nonzero entries as in step 1, and choose an entry p whose chosen exponent is minimal. Step 1 implies that p divides every entry. Swap its row with row zero and its column with column zero. Let B be the resulting matrix. These swaps are implemented by invertible permutation matrices, B_(0,0) = p, and p still divides every entry of B.

4. For each i ≠ 0, choose r_i with B_(i,0) = r_i p and replace row i by row i minus r_i times row zero. Each replacement is invertible, its inverse adding that multiple back. Row zero remains unchanged, and the resulting first column is p followed by zeros. For each j ≠ 0, choose c_j with B_(0,j) = p c_j and subtract c_j times column zero from column j. These operations are also invertible. They clear the first row outside its first entry, and do not change entries below that row because column zero is already zero there. Consequently there are invertible matrices P_0 and Q_0, incorporating the swaps and these operations, such that P_0 D Q_0 is block diagonal with blocks p and an m-by-m matrix D'.

5. An invertible matrix has unit determinant: taking determinants of its product with its inverse gives a multiplicative inverse for its determinant. Hence det(P_0) det(D) det(Q_0) is nonzero. The determinant of the block matrix is p det(D'), so det(D') ≠ 0. The induction hypothesis supplies invertible P' and Q' and nonzero diagonal entries d' with P' D' Q' = diagonal(d').

6. Let L and R be the block matrices diagonal(1,P') and diagonal(1,Q'). Their inverses are diagonal(1,(P')⁻¹) and diagonal(1,(Q')⁻¹), respectively. Set P = L P_0 and Q = Q_0 R. Products of invertible matrices are invertible. Block multiplication gives P D Q = diagonal(p, diagonal(d')). Define d(0) = p and d(i.succ) = d'(i). This block matrix is diagonal(d), and every entry of d is nonzero by the choice of p and the induction hypothesis. This completes the induction and the theorem.

## Key steps

1. Use uniformizer factorizations to obtain divisibility from an inequality of natural exponents.
2. Handle the empty matrix explicitly.
3. Choose a nonzero pivot with minimal exponent and move it to the first diagonal position.
4. Use invertible row and column operations to isolate a one-by-one block.
5. Deduce that the remaining block has nonzero determinant and apply induction.
6. Extend the inductive transformations by identity blocks and compose them.

## Reference use

### local-project

Queries:
- `rg -n 'ord_coe_unit|ord_coe_irreducible|exists_unit_mul_zpow|ord_coe_nonneg|structure Place|def ord|IsDiscreteValuationRing' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_*.lean`
- `rg -n 'length_eq_add_of_exact|length_pi|length_eq_one|length_eq_zero|length.*equiv|length.*quotient|length_prod' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `rg -n 'eq_unit_mul_pow_irreducible|exists_irreducible|class IsDiscreteValuationRing|irreducible.*maximalIdeal|length|cokernel' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/*.lean`
- `rg -n 'length.*det|det.*length|ord.*length|length.*ord|cokernel.*diagonal|diagonal.*cokernel' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra`
- `rg -n 'p06_9e0f5043ff_dlen_(scalar_quotient|matrix_diagonalization|diagonal_cokernel)' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json Definitions Submission.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/FreeModule/PID.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Quotient/Pi.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/OrderOfVanishing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/Submission.frozen-source-check.log`

The project supplies the place DVR instance and normalized order laws. Mathlib supplies unit-times-uniformizer factorization, length_quotient_pow_maximalIdeal, exact-sequence length additivity, LinearEquiv.length_eq, length_pi_of_fintype, submodule Smith normal form, matrix-to-linear-map multiplication, and quotient/product infrastructure. No matching determinant-length or diagonal-cokernel theorem was found. Ring.ord is a different, ENat-valued definition and cannot silently replace the project's integer-valued order. The proposed names have no collision in the inspected DAG or project declarations. Project HEAD and mathlib HEAD match the manifest; mathlib has no tracked modifications, and the seven compared interface files match the snapshot byte-for-byte. Existing audit logs report only propext, Classical.choice and Quot.sound for length_eq_add_of_exact and exists_unit_mul_zpow, but do not certify these new children. No Lean or Lake executable is available in this session. Earlier authoritative Submission checks failed on three unavailable attribute targets. Consequently, fresh elaboration after the authoritative import, inferred-instance checks, complete transitive axiom checks, and comparator acceptance remain unverified activation gates.
