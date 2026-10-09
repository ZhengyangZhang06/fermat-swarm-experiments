# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_hopf_envelope-a1`
- Child DAG node: `root.finite_hopf_envelope-a1.coefficient_matrix-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let n=dim_k V and choose a basis v_i of V indexed by Fin n. Their images in H remain linearly independent because inclusion of V is injective. Extend this family to a basis of H. Such an extension exists by taking a maximal independent set containing the family: chain unions remain independent, and maximality forces spanning. Define φ_i:H→k to be the coordinate functional of v_i in this extended basis. Then φ_i(v_j)=δ_ij.
2. For each j, the stability hypothesis expresses Δ(v_j) as a finite linear combination of tensors a⊗b with a∈V. Absorb scalar coefficients into a, and expand each such a in the basis v_i. Collecting terms gives Δ(v_j)=Σ_i v_i⊗c_ij for elements c_ij∈H. These coefficients are unique: contracting the first tensor factor by φ_i recovers c_ij. They form a matrix c indexed by Fin n.
3. Apply coassociativity to v_j and substitute the expressions from step 2. In H⊗H⊗H this yields Σ_i v_i⊗Δ(c_ij)=Σ_l Σ_i v_i⊗c_il⊗c_lj. Contract the first factor by φ_i. The resulting equality is Δ(c_ij)=Σ_l c_il⊗c_lj, proving the required comultiplication formula.
4. Right counitality applied to step 2 gives v_j=Σ_i ε(c_ij)v_i. Applying φ_i to this equality gives ε(c_ij)=φ_i(v_j)=δ_ij. This proves the required counit formula.
5. Left counitality applied to the same expression gives v_j=Σ_i ε(v_i)c_ij. Consequently every basis vector v_j lies in the k-linear span of all entries of c. Since every x∈V is a linear combination of these basis vectors, every such x lies in that span.
6. If n=0, the basis is empty and V is zero. The containment in step 5 is then containment of zero in the span of an empty set, while both indexed formulas are vacuous. Thus the construction proves the statement in every dimension.

## Key steps

1. Choose a finite basis and extend its coordinate functionals to H.
2. Expand each basis-vector comultiplication in that basis to define c.
3. Extract first-factor coefficients from coassociativity.
4. Extract coefficients from right counitality to obtain the identity counit matrix.
5. Use left counitality to place V in the span of the matrix entries.

## Reference use

### local-project

Queries:
- `antipode.*(mul|one)|def antipode|antipodeAlgHom|exists.*(subcoalgebra|Subcoalgebra)|FiniteDimensional|finite.*[Cc]oalgebra`
- `FiniteDimensional|finiteDimensional|exists.*[Ss]ubcoalgebra|exists.*[Ss]ubcomodule|finite.*[Ss]ubcoalgebra`
- `theorem (det_mul|det_map|mul_adjugate|adjugate_mul)|def adjugate|theorem.*det.*one|map_det`
- `exists_extension|extend|exists.*basis|finite_basis|finBasis`
- `finiteType_adjoin|finiteType.*fg|fg.*finiteType|fg_adjoin|adjoin.*finite`
- `p05_fhe_(stable_subspace|coefficient_matrix|determinant_inverse)_a5b449214a`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p05_fhe_typecheck_a5b449214a.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean HeaderPolicyCheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/FiniteType.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge/HeaderPolicyCheck.lean`
- `/tmp/p05_fhe_typecheck_a5b449214a.lean`

The clean snapshots match project 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Coalgebra.Basic supplies finite tensor representations, coassociativity and counitality; the coalgebra-directory search found no finite-dimensional subcomodule existence theorem. Basis.VectorSpace supplies LinearMap.exists_extend. HopfAlgebra.Convolution already supplies antipodeAlgHom. The matrix files supply det_mul, RingHom.map_det, mul_adjugate and adjugate_mul; FiniteType supplies adjoin_of_finite. All three proposed types elaborated after import Submission under Lean 4.33.1. Kernel-checked diagnostic equalities confirmed ordinary multiplication for matrices constructed with Matrix.of. Audited infrastructure depends only on propext, Classical.choice and Quot.sound; all nine checked dependencies are clean and pinned. The existing private compiler copies were verified against policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: only listed lines 10–11 are omitted, original hash 2e81f3c63685285e1af52e3dee0c135a8a7c8e9f37be7ad076712f55790c632c reversibly yields build hash d10948155ea0e92408d3ce320bdd5db3b7f00b622f4c9de9c98f040a414fa2f6, and the rerun Lean probe confirmed every omitted target absent. The proposed names have no current DAG or searched library collisions. These are decomposition diagnostics, not comparator acceptance of theorem proofs.
