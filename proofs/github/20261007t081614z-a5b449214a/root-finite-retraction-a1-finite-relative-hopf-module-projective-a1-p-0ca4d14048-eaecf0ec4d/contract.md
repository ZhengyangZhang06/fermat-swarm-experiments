<!-- theorem-id: fermat-p05/root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.redundant_generator_relations-a1 -->

## Theorem `Submission.p05_pie_redundant_generator_relations_a5b449214a`

Let R be a commutative ring and M an R-module with commutative additive group. Let n,p,t be natural numbers, P an n-by-p matrix, A an n-by-t matrix, and π:R^n→M and ψ:R^t→M R-linear maps. Assume ker(π)=im(P) and π(Ay)=ψ(y) for every y∈R^t. Set T=[[P,−A],[0,I_t]], with row set Fin n ⊕ Fin t and column set Fin p ⊕ Fin t. For every z on the row set, write x(i)=z(inl i) and y(j)=z(inr j). Then π(x)+ψ(y)=0 if and only if there exists w on the column set with T w=z. No surjectivity is assumed.

Node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.redundant_generator_relations-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/281

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_pie_redundant_generator_relations_a5b449214a`

```lean
∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (n p t : ℕ) (P : Matrix (Fin n) (Fin p) R) (A : Matrix (Fin n) (Fin t) R) (π : (Fin n → R) →ₗ[R] M) (ψ : (Fin t → R) →ₗ[R] M) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin) (_hA : ∀ y : Fin t → R, π (A.mulVecLin y) = ψ y), let T : Matrix (Fin n ⊕ Fin t) (Fin p ⊕ Fin t) R := Matrix.fromBlocks P (-A) 0 (1 : Matrix (Fin t) (Fin t) R); ∀ z : (Fin n ⊕ Fin t) → R, (π (fun i => z (Sum.inl i)) + ψ (fun j => z (Sum.inr j)) = 0) ↔ ∃ w : (Fin p ⊕ Fin t) → R, T.mulVecLin w = z
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

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.redundant_generator_relations-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write z=(x,y), meaning x(i)=z(inl i) and y(j)=z(inr j). For w=(u,v), block multiplication gives T w=(P u−A v,v), since the lower blocks of T are zero and the identity matrix. These are equations of vectors over R.
2. Suppose π(x)+ψ(y)=0. The hypothesis π(A y)=ψ(y) and linearity imply π(x+A y)=0. Thus x+A y belongs to ker π, which equals the image of P by hypothesis. Choose u with P u=x+A y and define w=(u,y). Step 1 gives T w=(P u−A y,y)=(x,y)=z. This proves the forward implication.
3. Conversely, suppose T w=z and write w=(u,v). Step 1 implies x=P u−A v and y=v. Since P u lies in the image of P=ker π, we have π(P u)=0. Consequently π(x)+ψ(y)=π(P u)−π(A v)+ψ(v)=0−ψ(v)+ψ(v)=0.
4. Both implications hold for every z. They use no surjectivity assumption and remain valid when any index set is empty, since the corresponding vector and matrix formulas use empty sums.

## Key steps

1. Compute T(u,v)=(Pu−Av,v).
2. Turn an enlarged relation into x+Ay∈ker(π).
3. Lift x+Ay through P and construct the preimage (u,y).
4. For the converse, use π(Pu)=0 and π(Av)=ψ(v) to cancel.

## Reference use

### local-project

Queries:
- `determinantal|fittingIdeal|fitting ideal|minor.*ideal|ideal.*minor`
- `det_mul|det_mul.*sum|det_succ|det_fromBlocks|det_submatrix|det_eq_zero_of`
- `fromBlocks_mulVec|mulVec_fromBlocks|mulVecLin|range_mulVecLin`
- `p05_pie_|minor_product|minor_descending|identity_stabilization|redundant_kernel`
- `git show ca1bb49d173a82f6c760dd27fdde39c92765501e:Submission.lean`
- `python3 /tmp/p05-pie-decomposition-eufao_g3/validate.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Data/Matrix/Block.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p05-pie-decomposition-eufao_g3/ChildTypes.lean`
- `/tmp/p05-pie-decomposition-eufao_g3/ChildTypes.lean.log`
- `/tmp/p05-pie-decomposition-eufao_g3/HeaderAbsence.lean`
- `/tmp/p05-pie-decomposition-eufao_g3/binding.json`

The searched algebra sources contain no matching determinantal-ideal or Fitting-ideal presentation-invariance theorem. Determinant/Basic.lean provides empty determinants, alternating determinant expansions, Laplace expansion, and block determinants; ToLin.lean identifies matrix images with column spans and matrix multiplication with composition; Data/Matrix/Block.lean supplies block multiplication formulas. Verified clean snapshot revisions 2fdd42759f4ab17640ac773289b521dd69d4b26e and db584cd6d46c92f209a44c0f1c829460d327499d, and all nine installed dependency pins. All four literal child types elaborate after import Submission. Anonymous Lean checks confirm matrix multiplication and identity-block semantics. Six inspected infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. Proposed names are unreserved across the checked 36-node DAG. Disposable compiler copies omit exactly policy-listed lines 10–11; the policy digest matches 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, Lean confirmed absence of all 13 targets, and binding.json records reversible original/build hashes. These are decomposition diagnostics, not comparator acceptance of child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
