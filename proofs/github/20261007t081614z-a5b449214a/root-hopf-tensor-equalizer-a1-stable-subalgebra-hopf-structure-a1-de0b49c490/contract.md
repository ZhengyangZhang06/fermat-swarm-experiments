<!-- theorem-id: fermat-p05/root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1 -->

## Theorem `Submission.p05_hte_stable_subalgebra_hopf_structure_a5b449214a`

Let k be a field, H a commutative Hopf k-algebra, and D a k-subalgebra of H. Suppose Δ_H(d) lies in the k-linear span of a⊗b with a,b∈D for every d∈D, and S_H(D)⊆D. Then D admits a Hopf k-algebra structure whose algebra structure is its existing subalgebra structure, together with a bialgebra homomorphism ι:D→H equal to inclusion on every element and satisfying ι(S_D(d))=S_H(ι(d)) for every d∈D.

Node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/233

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/289, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/290

## Lean problem

Declaration: `Submission.p05_hte_stable_subalgebra_hopf_structure_a5b449214a`

```lean
∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (D : Subalgebra k H) (hΔ : ∀ x ∈ D, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k H H | ∃ a ∈ D, ∃ b ∈ D, t = TensorProduct.tmul k a b}) (hS : ∀ x ∈ D, HopfAlgebra.antipode k x ∈ D), ∃ hD : HopfAlgebra k D, hD.toHopfAlgebraStruct.toBialgebra.toAlgebra = (inferInstance : Algebra k D) ∧ (letI : Algebra k D := hD.toHopfAlgebraStruct.toBialgebra.toAlgebra; letI : Module k D := Algebra.toModule; letI : HopfAlgebra k D := hD; ∃ ι : BialgHom k D H, (∀ d : D, ι d = (d : H)) ∧ ∀ d : D, ((HopfAlgebra.antipode k d : D) : H) = HopfAlgebra.antipode k (d : H))
```

### Frozen project context

`Fermat/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean` at `2fdd42759f4ab17640ac773289b521dd69d4b26e` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.hopfKer_eq_of_surjective_of_ker_eq_span
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    {B : Type w} [CommRing B] [Bialgebra k B] (q : H →ₐc[k] B) (hq : Function.Surjective q)
    (hker : RingHom.ker (q : H →+* B) =
      Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}) :
    HopfAlgebra.hopfKer q = K := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

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


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/696

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
