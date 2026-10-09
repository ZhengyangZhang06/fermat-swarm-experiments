<!-- theorem-id: fermat-p05/root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1.algebra_coaction_twist-a1 -->

## Theorem `Submission.p05_ct_algebra_a5b449214a`

Let k be a field, let A and H be commutative Hopf k-algebras, and let ι:A→H be a k-bialgebra homomorphism. All tensor products are over k, and Δ_A denotes the comultiplication of A. There exists a k-algebra automorphism θ of A⊗H such that, for every a∈A and h∈H, θ(a⊗h)=((id_A⊗ι)(Δ_A(a)))(1⊗h), where multiplication is the tensor-product algebra multiplication.

Node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1.algebra_coaction_twist-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/283

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_ct_algebra_a5b449214a`

```lean
∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A] {H : Type*} [CommRing H] [HopfAlgebra k H] (ι : BialgHom k A H), ∃ θ : TensorProduct k A H ≃ₐ[k] TensorProduct k A H, ∀ (a : A) (h : H), θ (TensorProduct.tmul k a h) = (TensorProduct.map (LinearMap.id : A →ₗ[k] A) ι.toLinearMap) (Coalgebra.comul (R := k) a) * TensorProduct.tmul k (1 : A) h
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

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1.algebra_coaction_twist-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put S=A⊗_k H and denote the antipode and counit of A by S_A and ε_A. Write Δ_A(a)=Σa₁⊗a₂. Such notation abbreviates a finite tensor representation. Every expression below is obtained by applying linear maps induced by multiplication, ι and S_A, so its value is independent of the chosen representation.
2. Define prescriptions F(a,h)=Σa₁⊗ι(a₂)h and G(a,h)=Σa₁⊗ι(S_A(a₂))h. Explicitly, F(a,h)=((id_A⊗ι)(Δ_A(a)))(1⊗h), and G uses ι∘S_A in place of ι. Comultiplication, ι, S_A and h↦1⊗h are k-linear, while multiplication in S is k-bilinear. Hence F and G are separately k-linear in a and h. The tensor universal property therefore gives k-linear maps θ₀,ψ:S→S with θ₀(a⊗h)=F(a,h) and ψ(a⊗h)=G(a,h).
3. Since Δ_A and ι preserve multiplication, for a,b∈A and h,g∈H we have θ₀((a⊗h)(b⊗g))=Σa₁b₁⊗ι(a₂b₂)hg. Tensor-product multiplication gives θ₀(a⊗h)θ₀(b⊗g)=Σa₁b₁⊗(ι(a₂)h)(ι(b₂)g). Multiplicativity of ι and commutativity of H identify these two sums. Both sides of θ₀(xy)=θ₀(x)θ₀(y) are separately k-linear in x and y. Every tensor is a finite sum of pure tensors, so the equality holds for all x,y∈S.
4. Comultiplication and ι preserve the unit, hence θ₀(1⊗1)=1⊗1. Together with k-linearity this implies θ₀(c·1)=c·1 for every c∈k. Thus θ₀ is a unital k-algebra homomorphism.
5. Expanding θ₀ψ on a pure tensor gives Σ(a₁)₁⊗ι((a₁)₂)ι(S_A(a₂))h. Apply coassociativity of Δ_A, followed by the linear map sending x⊗y⊗z to x⊗ι(yS_A(z))h. This rewrites the result as Σa₁⊗ι((a₂)₁S_A((a₂)₂))h. The antipode identity Σb₁S_A(b₂)=ε_A(b)·1_A, and preservation of scalars by ι, reduce it to Σa₁⊗(ε_A(a₂)·h). Tensor balancing changes this to (Σ ε_A(a₂)·a₁)⊗h, which equals a⊗h by right counitality.
6. Expanding ψθ₀ gives Σ(a₁)₁⊗ι(S_A((a₁)₂))ι(a₂)h. Coassociativity, now followed by x⊗y⊗z↦x⊗ι(S_A(y)z)h, rewrites this as Σa₁⊗ι(S_A((a₂)₁)(a₂)₂)h. The other antipode identity ΣS_A(b₁)b₂=ε_A(b)·1_A reduces it to the same counit expression as in step 5, hence to a⊗h.
7. Both compositions θ₀ψ and ψθ₀ are k-linear and agree with the identity on every pure tensor. They consequently equal the identity on all of S. Thus θ₀ is bijective, with inverse ψ. The bijective k-algebra homomorphism θ₀ defines a k-algebra automorphism θ. Its value on each a⊗h is the formula from step 2, exactly as required.

## Key steps

1. Construct θ₀ and its antipode-based candidate inverse ψ by the tensor universal property.
2. Prove θ₀ multiplicative on pure tensors and extend in both arguments.
3. Prove preservation of the unit and embedded k-scalars.
4. Use coassociativity and the id–antipode cancellation identity to show θ₀ψ=id.
5. Use coassociativity and the antipode–id cancellation identity to show ψθ₀=id.
6. Bundle the bijective algebra homomorphism as θ with the required formula.

## Reference use

### local-project

Queries:
- `Repr.arbitrary|coassociat|semilinear|tensor.*equiv|exists.*twist|antipode`
- `coassoc|counit.*rTensor|rTensor.*counit|arbitrary|sum_tmul`
- `coaction.*(twist|equiv)|twist.*(coaction|tensor)|p05_ct_(algebra|comodule|compatibility)_a5b449214a`
- `theorem tmul_mul_tmul|lemma tmul_mul_tmul|instance.*CommRing|def mulLeft`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean`

The project defines the induced algebra coaction. Coalgebra.Basic provides finite representations, coassociativity and counitality; HopfAlgebra.Basic provides both antipode cancellation identities; TensorProduct.Basic supplies tensor multiplication. No existing coaction-twist equivalence matched the search in the project and HopfAlgebra reference sources. Snapshot revisions match the manifest and are clean; installed dependency revisions also match their pins. Both proposed types elaborated after import Submission using Lean 4.33.1 in /tmp/p05-coaction-decomposition-h39p315q. The inferred multiplication was checked against Algebra.TensorProduct.tmul_mul_tmul. The inspected cancellation, coassociativity, counit and tensor-map declarations have only standard logical axioms. Private-copy header omissions matched the specified policy, and a fresh Lean probe confirmed all 13 omitted targets absent. These are decomposition diagnostics, not proof acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/450

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
