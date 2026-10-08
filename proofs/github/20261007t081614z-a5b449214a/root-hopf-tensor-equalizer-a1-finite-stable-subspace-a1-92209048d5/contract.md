<!-- theorem-id: fermat-p05/root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1 -->

## Theorem `Submission.p05_hte_finite_stable_subspace_a5b449214a`

Let k be a field and C a k-coalgebra whose underlying k-module is an additive commutative group. For every finite subset E of C there is a finite-dimensional k-subspace V of C containing E such that Δ_C(v) lies in the k-linear span of tensors a⊗b with a∈V and b∈C for every v∈V.

Node: `root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/233

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/277, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/278

## Lean problem

Declaration: `Submission.p05_hte_finite_stable_subspace_a5b449214a`

```lean
∀ {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C] (E : Finset C), ∃ V : Submodule k C, FiniteDimensional k V ∧ (∀ x ∈ E, x ∈ V) ∧ ∀ x ∈ V, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k C C | ∃ a ∈ V, ∃ b : C, t = TensorProduct.tmul k a b}
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


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
