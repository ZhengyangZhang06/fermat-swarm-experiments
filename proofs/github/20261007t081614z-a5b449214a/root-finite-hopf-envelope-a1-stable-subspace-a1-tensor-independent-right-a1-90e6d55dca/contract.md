<!-- theorem-id: fermat-p05/root.finite_hopf_envelope-a1.stable_subspace-a1.tensor_independent_right-a1 -->

## Theorem `Submission.p05_fhess_tensor_independent_right_a5b449214a`

Let k be a field and M,N be k-vector spaces. For every z∈M⊗ₖN, there exist a natural number n and families v:Fin n→M and w:Fin n→N such that w is k-linearly independent and z=Σᵢ vᵢ⊗wᵢ. The index set may be empty.

Node: `root.finite_hopf_envelope-a1.stable_subspace-a1.tensor_independent_right-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/246

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_fhess_tensor_independent_right_a5b449214a`

```lean
∀ {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M] {N : Type*} [AddCommGroup N] [Module k N] (z : TensorProduct k M N), ∃ (n : ℕ) (v : Fin n → M) (w : Fin n → N), LinearIndependent k w ∧ z = ∑ i : Fin n, TensorProduct.tmul k (v i) (w i)
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
- Child DAG node: `root.finite_hopf_envelope-a1.stable_subspace-a1.tensor_independent_right-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. By tensor-product induction, z has a finite expression z=Σᵣ aᵣ⊗bᵣ. Indeed, zero has the empty expression, a pure tensor has a one-term expression, and expressions for two tensors concatenate to give an expression for their sum.
2. Scan the finite list of vectors bᵣ, starting with the empty list, retaining a vector precisely when it is outside the span of those already retained. At every stage the retained vectors are independent: when adding b outside their span, a relation with nonzero coefficient c on b would express b as −c⁻¹ times a linear combination of the earlier vectors, a contradiction; if c=0, independence of the earlier vectors makes every coefficient zero. Every scanned vector belongs to the current span, because it was either retained or already belonged to the preceding span. Thus the final retained family w:Fin n→N is independent and spans every bᵣ.
3. For each r choose scalars λᵢᵣ with bᵣ=Σᵢ λᵢᵣwᵢ, and define vᵢ=Σᵣ λᵢᵣaᵣ. These are finite sums, and such coordinates exist by the spanning conclusion of step 2.
4. Tensor bilinearity and interchange of finite sums give z=Σᵣ aᵣ⊗(Σᵢ λᵢᵣwᵢ)=Σᵢ(Σᵣ λᵢᵣaᵣ)⊗wᵢ=Σᵢ vᵢ⊗wᵢ. Together with independence from step 2, this proves the assertion.
5. If no vector was retained, each bᵣ belongs to the span of the empty set and is therefore zero. Consequently z=0, and the empty families give the required expansion and vacuous independence.

## Key steps

1. Obtain a finite pure-tensor expression by tensor-product induction.
2. Extract an independent spanning subfamily of the finitely many right factors.
3. Expand each original right factor in that family.
4. Absorb its scalar coordinates into the left factors and interchange finite sums.
5. Handle the empty independent family by the zero tensor.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/327

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
