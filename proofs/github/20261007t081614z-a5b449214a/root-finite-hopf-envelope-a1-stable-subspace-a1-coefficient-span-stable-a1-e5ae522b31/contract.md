<!-- theorem-id: fermat-p05/root.finite_hopf_envelope-a1.stable_subspace-a1.coefficient_span_stable-a1 -->

## Theorem `Submission.p05_fhess_coefficient_span_stable_a5b449214a`

Let k be a field and C a k-vector space equipped with a coassociative comultiplication Δ:C→C⊗ₖC and a counit satisfying both counit identities. Let x∈C, let n be a natural number, and let v,w:Fin n→C satisfy that w is k-linearly independent and Δ(x)=Σᵢ vᵢ⊗wᵢ. Then V=spanₖ{vᵢ | i∈Fin n} is finite-dimensional, contains x, and satisfies Δ(y)∈spanₖ{a⊗b | a∈V, b∈C} for every y∈V.

Node: `root.finite_hopf_envelope-a1.stable_subspace-a1.coefficient_span_stable-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/246

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_fhess_coefficient_span_stable_a5b449214a`

```lean
∀ {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C] (x : C) (n : ℕ) (v w : Fin n → C), LinearIndependent k w → Coalgebra.comul (R := k) x = (∑ i : Fin n, TensorProduct.tmul k (v i) (w i)) → FiniteDimensional k (Submodule.span k (Set.range v)) ∧ x ∈ Submodule.span k (Set.range v) ∧ ∀ y ∈ Submodule.span k (Set.range v), Coalgebra.comul (R := k) y ∈ Submodule.span k {t : TensorProduct k C C | ∃ a ∈ Submodule.span k (Set.range v), ∃ b : C, t = TensorProduct.tmul k a b}
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

- Parent DAG node: `root.finite_hopf_envelope-a1.stable_subspace-a1`
- Child DAG node: `root.finite_hopf_envelope-a1.stable_subspace-a1.coefficient_span_stable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put V=spanₖ{vᵢ | i∈Fin n} and W=spanₖ{a⊗b | a∈V, b∈C}. The n vectors vᵢ generate V, so V is finite-dimensional.
2. Extend the independent family w to a basis of C. For completeness, consider independent subsets containing its image, ordered by inclusion. The union of a chain is independent because every finite relation is contained in one member of the chain. The maximality principle therefore gives a maximal such independent set. It spans C: otherwise a vector outside its span could be adjoined while preserving independence, since a relation with nonzero coefficient on that vector would put it in the old span. Thus this set is a basis containing all wᵢ. For each j∈Fin n, define φⱼ:C→k to be the coordinate functional of wⱼ in this basis. Uniqueness of finite basis expansions makes φⱼ linear and gives φⱼ(wᵢ)=1 when i=j and 0 otherwise.
3. Define a linear contraction Dⱼ:C⊗ₖC→C by Dⱼ(a⊗b)=φⱼ(b)a. This is well-defined because the displayed expression is bilinear. Define also Tⱼ:(C⊗ₖC)⊗ₖC→C⊗ₖC by Tⱼ(z⊗c)=φⱼ(c)z, again using bilinearity.
4. Coassociativity applied to x and the assumed expansion gives, under the tensor associator α, α(Σᵢ Δ(vᵢ)⊗wᵢ)=Σᵢ vᵢ⊗Δ(wᵢ). Apply Tⱼ after α⁻¹. The left side becomes Σᵢ φⱼ(wᵢ)Δ(vᵢ)=Δ(vⱼ). On a pure tensor a⊗(b⊗c), the right-side contraction is φⱼ(c)(a⊗b)=a⊗Dⱼ(b⊗c); linearity extends this computation to every tensor. Hence Δ(vⱼ)=Σᵢ vᵢ⊗Dⱼ(Δ(wᵢ)).
5. Every vᵢ belongs to V, so each pure tensor on the right of the identity in step 4 is a generator of W. Thus Δ(vⱼ)∈W for every j. Every y∈V is a finite linear combination of the vⱼ. Since Δ is linear and W is a subspace, Δ(y)∈W for every y∈V.
6. Write ε for the counit. Apply the linear map a⊗b↦ε(b)a to Δ(x)=Σᵢ vᵢ⊗wᵢ. The right counit identity makes the left side x, giving x=Σᵢ ε(wᵢ)vᵢ. Therefore x∈V.
7. These arguments include n=0: the last identity gives x=0, V is the zero subspace, and Δ(0)=0 belongs to W. Consequently finite dimension, containment, and stability hold in every case.

## Key steps

1. Define the finite coefficient span V and its associated tensor span W.
2. Extend the independent right factors to a basis and obtain coordinate functionals.
3. Construct linear contractions on the last tensor factor.
4. Contract coassociativity to express each Δ(vⱼ) with first factors in V.
5. Extend stability from the generators to all of V by linearity.
6. Apply right counitality to recover x as a linear combination of the vᵢ.
7. Include the empty-family case.

## Reference use

### local-project

Queries:
- `finiteDimensional|finite_dimensional|subcomodule|right.*coideal|exists.*tmul|linearIndependent`
- `exists.*[Ll]inearIndependent|[Ll]inearIndependent.*(exists|tmul)|[Ll]inearIndependent.*(right|snd)`
- `coassoc|counit|exists_sum_tmul_eq|exists.*(basis|Basis)|exists_extend|extend.*linear|extend.*apply`
- `p05_fhess_(tensor_independent_right|coefficient_span_stable)_a5b449214a`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p05_fhess_types_a5b449214a.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean HeaderPolicyCheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Finiteness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge/HeaderPolicyCheck.lean`
- `/tmp/p05_fhess_types_a5b449214a.lean`

The clean reference snapshots match project 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. TensorProduct.exists_sum_tmul_eq supplies finite pure-tensor expansions; Basis.VectorSpace supplies basis extension and LinearMap.exists_extend; Coalgebra.Basic supplies coassociativity and right counitality. Searches found no matching independent-right-factor expansion or finite-dimensional subcomodule existence theorem in the searched tensor-product and coalgebra directories. Both proposed names have no current DAG or searched-source collisions. Both exact types elaborated after import Submission under the pinned compiler. The six audited infrastructure declarations have transitive axioms contained in propext, Classical.choice and Quot.sound; all nine dependency revisions matched their pins with clean tracked sources. Reviewed frozen_header_repair evidence matches policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96. Only listed lines 10–11 were omitted in existing private compiler copies; original hash 2e81f3c63685285e1af52e3dee0c135a8a7c8e9f37be7ad076712f55790c632c reversibly yields build hash d10948155ea0e92408d3ce320bdd5db3b7f00b622f4c9de9c98f040a414fa2f6. The rerun Lean probe confirmed all omitted targets absent. These checks validate decomposition interfaces and infrastructure, not comparator acceptance of theorem proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/311

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
