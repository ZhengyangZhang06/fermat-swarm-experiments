# Parent-supplied natural-language proof

- Parent DAG node: `root.hopf_tensor_equalizer-a1`
- Child DAG node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Give D its existing commutative ring and k-algebra structures, and write i:D→H for inclusion. Extend a k-basis of D, viewed through i, to a basis of H. Sending the original basis vectors back to D and the added vectors to zero defines a k-linear map r:H→D with r∘i=id_D.
2. The maps i₂=i⊗i and i₃=i⊗i⊗i are injective because r⊗r and r⊗r⊗r are left inverses, with the usual associators understood. The image of i₂ is exactly the k-linear span of the tensors a⊗b with a,b∈D: pure tensors generate D⊗D, and each specified generator is the image of a pure tensor in D⊗D.
3. For d∈D, hΔ puts Δ_H(i(d)) in this image. Define Δ_D(d) as its unique preimage under i₂. Injectivity of i₂ and linearity of Δ_H show that Δ_D preserves sums and k-scalars. Since the tensor inclusion preserves multiplication and the unit, applying i₂ to Δ_D(de)=Δ_D(d)Δ_D(e) and Δ_D(1)=1 gives the corresponding identities in H⊗H. Injectivity proves both identities in D⊗D.
4. Define ε_D=ε_H∘i. This is k-linear and preserves multiplication and the unit. Apply i₃ to the two iterated coproducts of d. Naturality of tensor maps and i₂Δ_D=Δ_Hi identify their images with the two iterated coproducts of i(d), which agree by coassociativity of H. Injectivity gives coassociativity in D. Applying i to each of the two counit composites gives the corresponding counit composite in H, hence i(d); injectivity gives both counit identities in D. These operations equip the existing k-algebra D with a bialgebra structure.
5. By hS define S_D(d) to be S_H(i(d)), regarded as an element of D. Linearity follows from linearity of S_H and injectivity of i. Apply i to each of m_D(S_D⊗id)Δ_D(d) and m_D(id⊗S_D)Δ_D(d). Their images are respectively m_H(S_H⊗id)Δ_H(i(d)) and m_H(id⊗S_H)Δ_H(i(d)), both equal to ε_H(i(d))1_H. Since i(ε_D(d)1_D) has this same value, injectivity gives both antipode identities in D.
6. Thus these operations define hD:HopfAlgebra k D, using precisely the preexisting algebra structure, so the required equality of algebra structures holds. The original inclusion i preserves the algebra operations, Δ, and ε by construction, and therefore defines the required bialgebra homomorphism ι. Its underlying function is inclusion and the equality involving antipodes is exactly the definition of S_D.

## Key steps

1. Split the vector-space inclusion by extending a basis.
2. Use tensor powers of the splitting to prove injectivity and identify the double tensor image.
3. Restrict comultiplication and transfer its algebra and coassociativity identities.
4. Restrict the counit and antipode and transfer their identities.
5. Package the structure with the unchanged algebra structure and compatible inclusion.

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
