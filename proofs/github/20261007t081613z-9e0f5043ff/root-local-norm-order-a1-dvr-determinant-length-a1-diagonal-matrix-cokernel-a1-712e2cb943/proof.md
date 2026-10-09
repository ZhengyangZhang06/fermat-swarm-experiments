# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix R, m, D, P, Q and d satisfying the hypotheses. Write V = R^(Fin m) and W = ∏_i R/(d(i)). Choose inverse matrices P⁻¹ and Q⁻¹ from the unit hypotheses. Matrix multiplication on column vectors makes P and Q into R-linear automorphisms of V. The identity P D Q = diagonal(d) means that P(D(Qz)) has i-th coordinate d(i)z(i) for every z ∈ V.

2. Define an R-linear map F : V → W by F(x)(i) = the class of (Px)(i) modulo (d(i)). It is linear because multiplication by P is R-linear and each coordinate quotient map is R-linear; W has its coordinatewise R-module structure.

3. If x = Dy lies in the image of D, set z = Q⁻¹y. Then y = Qz, so Px = P D Q z = diagonal(d)z. Every coordinate of Px lies in the corresponding principal ideal (d(i)), and therefore F(x) = 0. Thus the image of D is contained in the kernel of F.

4. Conversely, suppose F(x) = 0. For each i, membership (Px)(i) ∈ (d(i)) supplies z(i) ∈ R with (Px)(i) = d(i)z(i). Choose these finitely many witnesses to form z ∈ V. Then Px = diagonal(d)z = P D Q z. Since P acts injectively, x = D(Qz). Hence x lies in the image of D. Together with step 3, this proves ker(F) = image(D).

5. The map F is surjective. Given w ∈ W, choose a representative y(i) ∈ R of each quotient coordinate w(i), and form y ∈ V. Set x = P⁻¹y. Then Px = y, so F(x) = w. This argument also covers m = 0, when the coordinate choices are empty.

6. By step 3, F induces an R-linear map from V/image(D) to W. It is injective by step 4 and surjective by step 5. Its inverse is linear: uniqueness of preimages under a bijective linear map identifies the preimage of a sum with the sum of preimages, and likewise for scalar multiples. Thus the induced map is an R-linear equivalence. This supplies the required inhabitant of Nonempty.

## Key steps

1. Interpret the two matrix units as linear automorphisms of the coordinate module.
2. Map a vector to the coordinate residue classes of its image under P.
3. Prove that the image of D is contained in the kernel using the inverse of Q.
4. Prove the reverse inclusion by choosing coordinate divisibility witnesses and cancelling P.
5. Prove surjectivity by choosing coordinate representatives and applying the inverse of P.
6. Descend to the quotient and obtain the linear equivalence.

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
