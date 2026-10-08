# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.bialgebra_restriction-a1.comul_alg_lift-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1-bia-e3066907da/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.bialgebra_restriction-a1`
- Child key: `comul_alg_lift`
- Declaration: `Submission.p05_hte_sshs_br_comul_alg_lift_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [Bialgebra k H] (D : Subalgebra k H) (_hΔ : ∀ x ∈ D, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k H H | ∃ a ∈ D, ∃ b ∈ D, t = TensorProduct.tmul k a b}), ∃ δ : D →ₐ[k] TensorProduct k D D, ∀ d : D, (Algebra.TensorProduct.map D.val D.val) (δ d) = Coalgebra.comul (R := k) (d : H)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
