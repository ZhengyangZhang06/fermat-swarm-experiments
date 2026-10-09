<!-- theorem-id: fermat-p05/root.canonical_map_injective-a1.canonical_balanced_lift-a1 -->

## Theorem `Submission.p05_canonical_balanced_lift_a5b449214a`

Let k be a field, H a commutative Hopf k-algebra, K a k-subalgebra of H, B a commutative k-bialgebra, and q:H→B a bialgebra homomorphism. Give H its K-algebra structure by inclusion and put ρ=(id_H⊗q)Δ_H. Assume ρ(t)=t⊗1_B for every t∈K. There exists a k-algebra homomorphism β:H⊗_K H→H⊗_k B satisfying β(a⊗_K b)=(a⊗_k1_B)ρ(b) for every a,b∈H.

Node: `root.canonical_map_injective-a1.canonical_balanced_lift-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/236

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_canonical_balanced_lift_a5b449214a`

```lean
∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H) {B : Type*} [CommRing B] [Bialgebra k B] (q : BialgHom k H B) (hcoinv : ∀ t ∈ K, HopfAlgebra.coaction q t = TensorProduct.tmul k t (1 : B)), ∃ β : (TensorProduct K H H) →ₐ[k] (TensorProduct k H B), ∀ a b : H, β (TensorProduct.tmul K a b) = (TensorProduct.tmul k a (1 : B)) * HopfAlgebra.coaction q b
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
- Child DAG node: `root.canonical_map_injective-a1.canonical_balanced_lift-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write T=H⊗_K H and U=H⊗_k B, with their usual commutative tensor-algebra structures. Give U the K-action t•u=(t⊗_k1_B)u. Its restriction to k is the usual k-action, since the inclusion K→H is a k-algebra homomorphism.
2. The map ρ=(id_H⊗q)Δ_H is a k-algebra homomorphism: both Δ_H and the tensor product of id_H with q are k-algebra homomorphisms. Define F(a,b)=(a⊗_k1_B)ρ(b). Additivity of both factors and distributivity make F additive in each variable.
3. For t∈K, multiplicativity and the coinvariance hypothesis give ρ(tb)=(t⊗_k1_B)ρ(b). Therefore F(ta,b)=(t⊗_k1_B)F(a,b)=F(a,tb). These identities also show K-linearity separately in both variables for the K-action on U. Thus F is K-bilinear.
4. The tensor-product universal property gives a K-linear map β:T→U with β(a⊗_K b)=F(a,b). Restricting scalars along k→K makes β k-linear, with the k-actions specified above.
5. For a,b,a′,b′∈H, the multiplication formula for T and multiplicativity of ρ give β((a⊗_K b)(a′⊗_K b′))=(aa′⊗_k1_B)ρ(bb′). Commutativity of U identifies this with ((a⊗_k1_B)ρ(b))((a′⊗_k1_B)ρ(b′)). Every tensor is a finite sum of pure tensors, so additivity and distributivity extend this equality to all pairs of elements of T.
6. The unit of T is 1_H⊗_K1_H. Its image is (1_H⊗_k1_B)ρ(1_H)=1_U. Since β is k-linear and preserves the unit, it preserves every k-scalar image. Together with additivity and step 5, this makes β a k-algebra homomorphism. Its defining pure-tensor formula is exactly the required formula.

## Key steps

1. Equip the target with the K-action through its first H-factor.
2. Use coinvariance to prove K-bilinearity of the canonical formula.
3. Apply the balanced tensor-product universal property and restrict scalars to k.
4. Check multiplicativity on pure tensors and extend by additivity.
5. Check the unit and scalar images to obtain the required algebra homomorphism.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/287

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
