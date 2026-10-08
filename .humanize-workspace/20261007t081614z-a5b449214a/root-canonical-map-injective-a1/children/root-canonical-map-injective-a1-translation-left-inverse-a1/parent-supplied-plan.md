# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.canonical_map_injective-a1.translation_left_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1-translation-left-inverse-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.canonical_map_injective-a1`
- Child key: `translation_left_inverse`
- Declaration: `Submission.p05_translation_left_inverse_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H) {B : Type*} [CommRing B] [Bialgebra k B] (q : BialgHom k H B) (β : (TensorProduct K H H) →ₐ[k] (TensorProduct k H B)) (hβ : ∀ a b : H, β (TensorProduct.tmul K a b) = (TensorProduct.tmul k a (1 : B)) * HopfAlgebra.coaction q b) (σ : B →ₐ[k] (TensorProduct K H H)) (hσ : ∀ b : H, σ (q b) = Algebra.TensorProduct.mapOfCompatibleSMul K k k H H (TensorProduct.map (HopfAlgebra.antipode k) (LinearMap.id : H →ₗ[k] H) (Coalgebra.comul (R := k) b))), ∃ γ : (TensorProduct k H B) →ₐ[k] (TensorProduct K H H), (∀ (a : H) (c : B), γ (TensorProduct.tmul k a c) = (TensorProduct.tmul K a (1 : H)) * σ c) ∧ Function.LeftInverse γ β`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
