# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.finite_family_dividing_member-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix A, ι, and a satisfying the hypotheses. By IsDiscreteValuationRing.exists_irreducible, choose an irreducible element π of A.
2. Let S consist of the indices i for which a(i) ≠ 0. This is a finite nonempty set: finiteness follows from Fintype ι, and nonemptiness is the hypothesis. For each i in S, apply IsDiscreteValuationRing.eq_unit_mul_pow_irreducible to choose e(i) ∈ ℕ and u(i) ∈ Aˣ such that a(i) = u(i)π^e(i), where units are coerced into A.
3. The finite nonempty set of chosen exponents has a minimum attained at an index i₀ in S. Put p = a(i₀), e₀ = e(i₀), and u₀ = u(i₀). Then p ≠ 0, p = u₀π^e₀, and e₀ ≤ e(j) for every j in S.
4. Fix any j : ι. If a(j) = 0, then p divides a(j), with quotient zero. Otherwise j belongs to S. Write e = e(j) and u = u(j), and define q = (u₀⁻¹ : A) · (u : A) · π^(e - e₀), taking u₀⁻¹ in the unit group. Commutativity, the unit inverse identity, and e₀ + (e - e₀) = e give p q = (u₀π^e₀)((u₀⁻¹ : A)uπ^(e - e₀)) = uπ^e = a(j). Thus p divides a(j) in this case as well.
5. Consequently i₀ satisfies both required conclusions: a(i₀) ≠ 0 and a(i₀) divides every a(j).

## Key steps

1. Choose an irreducible uniformizer.
2. Factor each nonzero family member as a unit times a natural power of the uniformizer.
3. Choose a member attaining the minimum exponent on the finite nonempty support.
4. Construct a divisibility quotient using the inverse unit and the exponent difference; handle zero members separately.

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
