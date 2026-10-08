# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.canonical_map_injective-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `canonical_map_injective`
- Declaration: `Submission.p05_canonical_map_injective_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H) (hΔ : (∀ x ∈ K, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k H H | ∃ a ∈ K, ∃ b ∈ K, t = TensorProduct.tmul k a b})) (hS : (∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)) {B : Type*} [CommRing B] [Bialgebra k B] (q : BialgHom k H B) (hq : Function.Surjective q) (hker : (RingHom.ker (q : H →+* B) = Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0})), ∃ β : (TensorProduct K H H) →ₐ[k] (TensorProduct k H B), Function.Injective β ∧ ∀ a b : H, β (TensorProduct.tmul K a b) = (TensorProduct.tmul k a (1 : B)) * HopfAlgebra.coaction q b`

## Sibling prerequisites

- `root.subalgebra_coinvariant-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
