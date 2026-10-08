# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.canonical_map_injective-a1.canonical_balanced_lift-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1-canonical-balanced-lift-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.canonical_map_injective-a1`
- Child key: `canonical_balanced_lift`
- Declaration: `Submission.p05_canonical_balanced_lift_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H) {B : Type*} [CommRing B] [Bialgebra k B] (q : BialgHom k H B) (hcoinv : ∀ t ∈ K, HopfAlgebra.coaction q t = TensorProduct.tmul k t (1 : B)), ∃ β : (TensorProduct K H H) →ₐ[k] (TensorProduct k H B), ∀ a b : H, β (TensorProduct.tmul K a b) = (TensorProduct.tmul k a (1 : B)) * HopfAlgebra.coaction q b`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
