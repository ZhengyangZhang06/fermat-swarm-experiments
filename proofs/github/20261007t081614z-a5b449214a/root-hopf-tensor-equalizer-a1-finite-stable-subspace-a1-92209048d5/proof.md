# Parent-supplied natural-language proof

- Parent DAG node: `root.hopf_tensor_equalizer-a1`
- Child DAG node: `root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix f∈C. Express Δ(f) as a finite sum of pure tensors. Let W be the finite-dimensional span of its second factors and choose a basis w₁,…,w_n of W. Expanding the second factors in this basis and collecting coefficients yields Δ(f)=Σ_i v_i⊗w_i. If W=0, take the empty sum. Extend this basis of W to a basis of C; the coordinate functions on the w_i, set to zero on the additional basis vectors, give k-linear maps λ_i:C→k satisfying λ_i(w_j)=δ_ij.
2. Coassociativity, after identifying the two parenthesizations of the triple tensor product, says Σ_j Δ(v_j)⊗w_j=Σ_j v_j⊗Δ(w_j). Applying id⊗id⊗λ_i gives Δ(v_i)=Σ_j v_j⊗(id⊗λ_i)(Δ(w_j)), where C⊗k is identified with C by c⊗a↦ac. Therefore each Δ(v_i) lies in the span of tensors whose first factors belong to V_f=span_k{v₁,…,v_n}.
3. The right counit identity gives f=Σ_i ε(w_i)v_i, so f∈V_f. This also shows f=0 in the empty-sum case. The subspace V_f is finite-dimensional, since it has a finite spanning family. Linearity of Δ and closure of the tensor span under addition and k-scalar multiplication imply the same stability property for every element of V_f.
4. For the given finite set E, perform this construction for each f∈E, and let V be the sum of these finitely many V_f. The union of their finite spanning families is finite and spans V, so V is finite-dimensional. Each f∈E belongs to V_f⊆V. Writing an element of V as a sum of elements from the V_f and applying linearity proves that its coproduct belongs to the span of tensors with first factor in V. For E empty take V=0. This proves all asserted properties.

## Key steps

1. Express each coproduct with linearly independent second factors.
2. Extend their coordinate functionals to the whole coalgebra.
3. Apply those functionals to coassociativity to obtain a finite stable span.
4. Use counitality to recover the original element.
5. Sum the stable spans for the finite set.

## Reference use

### local-project

Queries:
- `finiteDimensional|FiniteDimensional|exists.*[Ss]ub|finite.*[Cc]omodule|finite.*[Cc]oalgebra`
- `exists.*[Ff]in|exists.*fg|finite.*relation|[Ff]inite.*[Zz]ero|exists.*[Ss]ubmodule`
- `Subalgebra.*[Mm]odule|module.*[Cc]omp|compHom|instance.*[Mm]odule`
- `coassoc|rTensor_counit|lTensor_counit`
- `p05_hte_stable_subalgebra_hopf_structure_a5b449214a|p05_hte_finite_stable_subspace_a5b449214a|p05_hte_finite_tensor_zero_witness_a5b449214a|HopfKerHopf`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Bialgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Finiteness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1/decomposition-hte-diagnostics/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1/decomposition-hte-diagnostics/challenge-types-instances-axioms.log`

The snapshot provides the tensor relation presentation, finite tensor expansions, basis extension, linear retractions, restricted scalar instances, and Hopf axioms. The searches found no matching finite stable-subspace or simultaneous scalar/submodule zero-witness theorem, and no proposed-name collisions or HopfKerHopf declarations in the searched libraries. Project 2fdd42759f4ab17640ac773289b521dd69d4b26e, mathlib db584cd6d46c92f209a44c0f1c829460d327499d, and all nine dependencies passed clean-pin checks. All three literal propositions elaborate after import Submission in both derived contexts. Explicit probes verify the constructed Hopf structure's algebra/module/coalgebra instances and the restricted scalar actions. Twelve infrastructure axiom closures contain only propext, Classical.choice and Quot.sound. Policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 was checked; only listed lines 10–11 were omitted in compiler copies, reversible hashes were validated, and Lean confirmed all 13 targets absent. Protected original inputs remain unchanged. These are decomposition diagnostics, not comparator acceptance of any theorem.
