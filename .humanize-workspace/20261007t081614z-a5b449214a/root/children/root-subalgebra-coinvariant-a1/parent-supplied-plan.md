# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.subalgebra_coinvariant-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-subalgebra-coinvariant-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `subalgebra_coinvariant`
- Declaration: `Submission.p05_subalgebra_coinvariant_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H) (hΔ : (∀ x ∈ K, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k H H | ∃ a ∈ K, ∃ b ∈ K, t = TensorProduct.tmul k a b})) {B : Type*} [CommRing B] [Bialgebra k B] (q : BialgHom k H B) (hker : (RingHom.ker (q : H →+* B) = Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0})), K ≤ HopfAlgebra.hopfKer q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
