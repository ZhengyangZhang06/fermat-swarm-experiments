# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.canonical_map_injective-a1.translation_descends-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1-translation-descends-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.canonical_map_injective-a1`
- Child key: `translation_descends`
- Declaration: `Submission.p05_translation_descends_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H) (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k H H | ∃ a ∈ K, ∃ b ∈ K, t = TensorProduct.tmul k a b}) (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) {B : Type*} [CommRing B] [Bialgebra k B] (q : BialgHom k H B) (hq : Function.Surjective q) (hker : RingHom.ker (q : H →+* B) = Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}), ∃ σ : B →ₐ[k] (TensorProduct K H H), ∀ b : H, σ (q b) = Algebra.TensorProduct.mapOfCompatibleSMul K k k H H (TensorProduct.map (HopfAlgebra.antipode k) (LinearMap.id : H →ₗ[k] H) (Coalgebra.comul (R := k) b))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
