# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.antipode_lift-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1-ant-764e99656f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1`
- Child key: `antipode_lift`
- Declaration: `Submission.p05_hte_sshs_antipode_lift_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [bA : Bialgebra k A] {H : Type*} [CommRing H] [HopfAlgebra k H] (ι : BialgHom k A H) (hι : Function.Injective ι) (hS : ∀ a : A, ∃ b : A, ι b = HopfAlgebra.antipode k (ι a)), ∃ hA : HopfAlgebra k A, hA.toHopfAlgebraStruct.toBialgebra = bA ∧ (letI : Algebra k A := hA.toHopfAlgebraStruct.toBialgebra.toAlgebra; letI : Module k A := Algebra.toModule; letI : Bialgebra k A := hA.toHopfAlgebraStruct.toBialgebra; letI : HopfAlgebra k A := hA; ∀ a : A, ι (HopfAlgebra.antipode k a) = HopfAlgebra.antipode k (ι a))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
