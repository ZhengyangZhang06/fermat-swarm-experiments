# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_hopf_envelope-a1.coefficient_matrix-a1`
- Child DAG node: `root.finite_hopf_envelope-a1.coefficient_matrix-a1.coalgebra_laws-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. The vectors v_i=(b_i:H) are linearly independent, since b is a basis and the inclusion V→H is injective. Extend their image to a basis B of H. To justify the extension, order the linearly independent subsets of H containing this image by inclusion. A chain union is independent because every finite relation is contained in one member of the chain. Zorn's lemma gives a maximal such subset B. If a vector were outside its span, adjoining that vector would preserve independence, contradicting maximality. Thus B spans H and is a basis. For each i, define φ_i:H→k to be the coordinate functional of v_i in B. Uniqueness of basis coordinates makes φ_i linear and gives φ_i(v_r)=δ_ir.
2. For each i, define a linear contraction U_i:H⊗(H⊗H)→H⊗H by U_i(x⊗z)=φ_i(x)•z. The defining expression is bilinear in x and z, so it induces a linear map by the tensor-product universal property. In particular U_i(v_r⊗z)=δ_ir•z.
3. Fix j. Coassociativity, with the canonical associator identifying (H⊗H)⊗H with H⊗(H⊗H), gives (id⊗Δ)Δ(v_j)=assoc((Δ⊗id)Δ(v_j)). Substitute the assumed expansion on the left to obtain ∑_r v_r⊗Δ(c_rj). On the right first expand Δ(v_j)=∑_l v_l⊗c_lj and then expand each Δ(v_l)=∑_r v_r⊗c_rl. Linearity and the defining action of the associator give the equality ∑_r v_r⊗Δ(c_rj)=∑_l ∑_r v_r⊗(c_rl⊗c_lj).
4. Apply U_i to this equality. Linearity moves U_i through both finite sums, and φ_i(v_r)=δ_ir removes every term except r=i. Hence Δ(c_ij)=∑_l c_il⊗c_lj. Since i and j were arbitrary, the comultiplication identity holds for every pair of indices.
5. Right counitality says that the linear map x⊗y↦ε(y)•x sends Δ(v_j) to v_j. Applying it to the assumed expansion yields v_j=∑_r ε(c_rj)•v_r. Apply φ_i and use its linearity and its values on the v_r. This gives δ_ij=∑_r ε(c_rj)φ_i(v_r)=ε(c_ij). Reversing the equality proves the required counit identity for every i,j.
6. When n=0 there are no pairs of indices i,j, so both universally quantified conclusions are vacuous. Thus both identities hold in all cases.

## Key steps

1. Extend the included basis to a basis of H and obtain coordinate functionals φ_i with φ_i(v_r)=δ_ir.
2. Define linear contraction of the first factor of H⊗(H⊗H).
3. Expand both sides of coassociativity using the given coefficient equations.
4. Contract the first factor to obtain Δ(c_ij)=∑ l, c_il⊗c_lj.
5. Apply right counitality and coordinate functionals to obtain ε(c_ij)=δ_ij.
6. Include the vacuous zero-dimensional case.

## Reference use

### local-project

Queries:
- `coassoc|counit.*comul|comul.*counit`
- `exists_extension|extend|exists.*basis|finite_basis|finBasis`
- `sum_repr|sum.*repr`
- `exists.*coefficient|coefficient.*matrix|matrix.*coefficient`
- `p05_cm_basis_expansion_a5b449214a|p05_cm_coalgebra_laws_a5b449214a`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p05_cm_types_a5b449214a.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean HeaderPolicyCheck.lean`
- `python3 /tmp/p05_cm_context_a5b449214a.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basis.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge/HeaderPolicyCheck.lean`
- `/tmp/p05_cm_types_a5b449214a.lean`
- `/tmp/p05_cm_context_a5b449214a.json`

The snapshots are clean at project 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine compiled dependencies match their pinned revisions and are clean. Relevant infrastructure includes Module.finBasis, Module.Basis.sum_repr, LinearMap.exists_extend, TensorProduct.eq_repr_basis_left, Coalgebra.coassoc_apply, and both counitality lemmas. The coefficient-matrix search found no matching theorem in the coalgebra/Hopf-algebra directories. Both proposed exact types elaborated after import Submission; their names are absent from the DAG, searched snapshot, and imported environment. The inspected infrastructure has only propext, Classical.choice, and Quot.sound as transitive axioms. Compiler-copy diagnostics verified policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, precisely the authorized omissions at lines 10–11, and reversible original/build hashes 2e81f3c63685285e1af52e3dee0c135a8a7c8e9f37be7ad076712f55790c632c and d10948155ea0e92408d3ce320bdd5db3b7f00b622f4c9de9c98f040a414fa2f6. The rerun Lean probe confirmed every omitted target absent. These checks validate decomposition inputs and types; they do not constitute comparator acceptance of child proofs.
