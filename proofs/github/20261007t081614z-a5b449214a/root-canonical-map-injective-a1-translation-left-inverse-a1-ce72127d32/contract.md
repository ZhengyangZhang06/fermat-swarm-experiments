<!-- theorem-id: fermat-p05/root.canonical_map_injective-a1.translation_left_inverse-a1 -->

## Theorem `Submission.p05_translation_left_inverse_a5b449214a`

Let k be a field, H a commutative Hopf k-algebra, K a k-subalgebra of H, B a commutative k-bialgebra, and q:H→B a bialgebra homomorphism. Give H its K-algebra structure by inclusion. Put T=H⊗_K H, U=H⊗_k B, ρ=(id_H⊗q)Δ_H, and let C:H⊗_k H→T send a⊗_k b to a⊗_K b. Suppose β:T→U and σ:B→T are k-algebra homomorphisms satisfying β(a⊗_K b)=(a⊗_k1_B)ρ(b) for all a,b∈H and σ(q(b))=C((S_H⊗id_H)Δ_H(b)) for every b∈H. There exists a k-algebra homomorphism γ:U→T such that γ(a⊗_k c)=(a⊗_K1_H)σ(c) for every a∈H,c∈B and γ(β(z))=z for every z∈T.

Node: `root.canonical_map_injective-a1.translation_left_inverse-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/236

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_translation_left_inverse_a5b449214a`

```lean
∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H) {B : Type*} [CommRing B] [Bialgebra k B] (q : BialgHom k H B) (β : (TensorProduct K H H) →ₐ[k] (TensorProduct k H B)) (hβ : ∀ a b : H, β (TensorProduct.tmul K a b) = (TensorProduct.tmul k a (1 : B)) * HopfAlgebra.coaction q b) (σ : B →ₐ[k] (TensorProduct K H H)) (hσ : ∀ b : H, σ (q b) = Algebra.TensorProduct.mapOfCompatibleSMul K k k H H (TensorProduct.map (HopfAlgebra.antipode k) (LinearMap.id : H →ₗ[k] H) (Coalgebra.comul (R := k) b))), ∃ γ : (TensorProduct k H B) →ₐ[k] (TensorProduct K H H), (∀ (a : H) (c : B), γ (TensorProduct.tmul k a c) = (TensorProduct.tmul K a (1 : H)) * σ c) ∧ Function.LeftInverse γ β
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

- Parent DAG node: `root.canonical_map_injective-a1`
- Child DAG node: `root.canonical_map_injective-a1.translation_left_inverse-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write S and ε for the antipode and counit. The map i:H→T given by i(a)=a⊗_K1_H is a k-algebra homomorphism, by the tensor multiplication and scalar formulas. Since σ is also a k-algebra homomorphism, the formula G(a,c)=i(a)σ(c) is k-bilinear. The tensor-product universal property gives a k-linear map γ:U→T satisfying γ(a⊗_k c)=(a⊗_K1_H)σ(c).
2. For pure tensors, multiplicativity of i and σ and commutativity of T give γ((a⊗c)(a′⊗c′))=i(aa′)σ(cc′)=i(a)σ(c)i(a′)σ(c′). Additivity and distributivity extend this equality to arbitrary tensors. Also γ(1_H⊗1_B)=i(1_H)σ(1_B)=1_T. The k-linearity of γ then implies preservation of k-scalars. Thus γ is a k-algebra homomorphism with the required formula.
3. Establish the cancellation identity Σb₁S(b₂)⊗_k b₃=1_H⊗_k b. Apply the linear map that multiplies the first factor by the antipode of the second factor and retains the third factor to (Δ_H⊗id_H)Δ_H(b). The antipode identity turns the result into ΣalgebraMap(k,H)(ε(b₁))⊗_k b₂. Moving each k-scalar to the second factor and using the left counit identity turns this into 1_H⊗_k b. Coassociativity permits the same identity to be read using (id_H⊗Δ_H)Δ_H(b). All displayed sums are finite tensor representations of these linear-map identities.
4. Fix a,b∈H. The hypothesis on β and the definition of ρ give β(a⊗_K b)=Σab₁⊗_k q(b₂). Apply γ, then its pure-tensor formula and the hypothesis on σ. This gives γβ(a⊗_K b)=Σ(ab₁⊗_K1_H)C((S⊗id_H)Δ_H(b₂))=Σab₁S(b₂)⊗_K b₃, where coassociativity identifies the nested comultiplications. Map the identity from step 3 through C and multiply by a⊗_K1_H. The resulting equality is exactly γβ(a⊗_K b)=a⊗_K b.
5. Both γβ and the identity on T are additive. Every element of T is a finite sum of pure tensors, so step 4 implies γ(β(z))=z for every z∈T. Thus γ is a left inverse of β. Together with its formula from step 1, it satisfies both required conjuncts.

## Key steps

1. Construct γ from the bilinear formula using the supplied translation homomorphism.
2. Verify that γ is an algebra homomorphism.
3. Derive the three-factor antipode cancellation identity from coassociativity and the counit law.
4. Expand γβ on pure tensors using the two supplied formulas.
5. Apply cancellation and extend by additivity to obtain the left-inverse identity.

## Reference use

### local-project

Queries:
- `antipode|coaction|hopfKer|TensorProduct`
- `antipode.*(mul|AlgHom)|baseChange|lift.*[Aa]lgHom|liftOf|ofSurjective|ker_le`
- `def (lift|map|includeLeft|includeRight)|lift_tmul|map_tmul|ofTower|tensor.*[Tt]ower|algebraMap_def`
- `p05_canonical_balanced_lift_a5b449214a|p05_translation_descends_a5b449214a|p05_translation_left_inverse_a5b449214a`
- `rg --files -uu -g dag.json /mnt/data/zhengyang-workspace/fermat-swarm-projects`
- `python3 .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/validate.py`
- `python3 .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/rerun_instances.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/TensorProduct/Maps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/CheckInstances.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/header-input-binding.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/report.json`

The snapshot provides coaction, antipodeAlgHom, tensor-algebra lifting, and mapOfCompatibleSMul; these require no new helper declarations. Project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and all nine dependency checkouts passed cleanliness and identity checks. Searches found no proposed-name collisions in the pinned Lean sources or local DAGs. All three literal child types elaborate after import Submission. Separate Lean probes verified inclusion actions, tensor multiplication, units, scalars, and the scalar-changing map. Eight infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. Disposable compiler copies followed the matching policy entry with digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: only lines 10–11 were omitted, reversible hashes were checked, and Lean confirmed all 13 targets absent. Frozen originals and the reviewed handoff remained unchanged. These are decomposition diagnostics; theorem acceptance still requires the configured comparator and independent review.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/313

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
