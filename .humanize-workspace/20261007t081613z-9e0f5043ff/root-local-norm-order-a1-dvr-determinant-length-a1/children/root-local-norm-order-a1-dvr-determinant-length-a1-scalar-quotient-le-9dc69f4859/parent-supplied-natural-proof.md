# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.scalar_quotient_length_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, E, v and a with a ≠ 0, and write A = v.toValuationSubring. The project instance makes A a discrete valuation ring. By IsDiscreteValuationRing.exists_irreducible, choose an irreducible π ∈ A. By IsDiscreteValuationRing.eq_unit_mul_pow_irreducible, choose n ∈ ℕ and u ∈ Aˣ with a = uπ^n. Here π ≠ 0, and (π) is the maximal ideal of A.

2. We verify the scalar length calculation. Put Q_j = A/(π^j) for j ∈ ℕ. Since π^0 = 1, Q_0 is the zero module and has length zero. The quotient A/(π) is a simple A-module: its submodules correspond to ideals containing the maximal ideal (π), so only zero and the whole quotient occur, and the quotient is nonzero. Its length is therefore one.

3. For each j ∈ ℕ, multiplication by π^j defines an A-linear map α_j : A/(π) → Q_(j+1), and reduction defines an A-linear map β_j : Q_(j+1) → Q_j. The first map is well-defined because π^j(π) ⊆ (π^(j+1)). It is injective: if π^j x = π^(j+1)y, cancellation of the nonzero π^j gives x = πy. The second map is well-defined and surjective because (π^(j+1)) ⊆ (π^j). Its kernel consists exactly of classes represented by π^j y, which is the image of α_j. Thus these maps form a short exact sequence.

4. Apply Module.length_eq_add_of_exact to this sequence. It gives length_A(Q_(j+1)) = 1 + length_A(Q_j). Induction starting at Q_0 proves length_A(Q_j) = j in ℕ∞ for every j. This is also the specialization of the pinned length_quotient_pow_maximalIdeal theorem using (π^j) = (π)^j.

5. Since u is a unit, (a) = (π^n): one inclusion follows from a = uπ^n and the other from π^n = u⁻¹a. Hence A/(a) and Q_n are the same quotient after this ideal equality, so length_A(A/(a)) = n.

6. The inclusion A → E is injective, so the images of u and π are nonzero. The project laws give order zero for the image of u and order one for the image of π. Repeated application of ord_mul, starting with ord_one, gives order n for the image of π^n. Applying ord_mul once more to a = uπ^n yields v.ord(algebraMap A E a) = 0 + n = n in ℤ. This n proves both required equalities.

## Key steps

1. Factor the nonzero scalar as a unit times a natural power of a uniformizer.
2. Identify the uniformizer quotient as a simple module of length one.
3. Construct and verify the short exact sequence connecting successive power quotients.
4. Induct using length additivity to compute every power-quotient length.
5. Remove the unit from the principal ideal and compute the normalized order of the same factorization.

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
