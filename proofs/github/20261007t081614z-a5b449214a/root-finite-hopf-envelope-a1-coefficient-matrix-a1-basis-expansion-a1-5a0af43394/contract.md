<!-- theorem-id: fermat-p05/root.finite_hopf_envelope-a1.coefficient_matrix-a1.basis_expansion-a1 -->

## Theorem `Submission.p05_cm_basis_expansion_a5b449214a`

Let k be a field, H a commutative Hopf k-algebra with comultiplication Δ, V a k-subspace of H, n a natural number, and b a basis of V indexed by Fin n. Write v_i for the image of b_i in H. Assume that Δ(x) belongs to span_k{a⊗y | a∈V, y∈H} for every x∈V. Then there exists c : Matrix (Fin n) (Fin n) H such that Δ(v_j)=∑_i v_i⊗c_ij for every j∈Fin n. All tensor products are over k.

Node: `root.finite_hopf_envelope-a1.coefficient_matrix-a1.basis_expansion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/247

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_cm_basis_expansion_a5b449214a`

```lean
∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (V : Submodule k H) (n : ℕ) (b : Module.Basis (Fin n) k V) (hV : ∀ x ∈ V, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k H H | ∃ a ∈ V, ∃ y : H, t = TensorProduct.tmul k a y}), ∃ c : Matrix (Fin n) (Fin n) H, ∀ j : Fin n, Coalgebra.comul (R := k) (b j : H) = ∑ i : Fin n, TensorProduct.tmul k (b i : H) (c i j)
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

- Parent DAG node: `root.finite_hopf_envelope-a1.coefficient_matrix-a1`
- Child DAG node: `root.finite_hopf_envelope-a1.coefficient_matrix-a1.basis_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put v_i=(b_i:H). For every a∈V, the basis expansion in V, followed by its linear inclusion into H, gives a=∑_i α_i v_i, where α_i is the i-th coordinate of a in b.
2. Let W be the set of tensors expressible as ∑_i v_i⊗d_i for some family d:Fin n→H. This is a k-subspace of H⊗H. The zero family represents zero. If d and e represent two tensors, d+e represents their sum by additivity in the second tensor factor. If d represents a tensor and r∈k, the family i↦r•d_i represents its scalar multiple by r, by bilinearity of the tensor product.
3. Every generator a⊗y with a∈V belongs to W. Indeed, using the coefficients from step 1 and the balancing identity for tensor products gives a⊗y=(∑_i α_i v_i)⊗y=∑_i v_i⊗(α_i•y). Therefore the k-linear span of all these generators is contained in W.
4. For each j, v_j∈V. The stability hypothesis and step 3 imply Δ(v_j)∈W. Hence choose d_j:Fin n→H such that Δ(v_j)=∑_i v_i⊗d_j(i). Define c=Matrix.of (fun i j => d_j(i)). Its entries satisfy c_ij=d_j(i), so the required equality holds for every j.
5. The construction also covers n=0: there is a unique empty matrix and there are no column indices j, so the asserted family of equalities is vacuous. Thus the conclusion holds for every natural number n.

## Key steps

1. Expand every vector of V in the prescribed finite basis.
2. Show that tensors of the form ∑ i, v_i⊗d_i form a subspace.
3. Place each generating tensor a⊗y in that subspace using basis expansion and tensor balancing.
4. Apply stability to each basis vector and assemble the chosen coefficient families into a matrix.
5. Observe that the empty-index case satisfies the conclusion.

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


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/296

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
