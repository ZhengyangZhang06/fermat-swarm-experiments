# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.hopf_tensor_equalizer-a1`
- Child key: `stable_subalgebra_hopf_structure`
- Declaration: `Submission.p05_hte_stable_subalgebra_hopf_structure_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (D : Subalgebra k H) (hΔ : ∀ x ∈ D, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k H H | ∃ a ∈ D, ∃ b ∈ D, t = TensorProduct.tmul k a b}) (hS : ∀ x ∈ D, HopfAlgebra.antipode k x ∈ D), ∃ hD : HopfAlgebra k D, hD.toHopfAlgebraStruct.toBialgebra.toAlgebra = (inferInstance : Algebra k D) ∧ (letI : Algebra k D := hD.toHopfAlgebraStruct.toBialgebra.toAlgebra; letI : Module k D := Algebra.toModule; letI : HopfAlgebra k D := hD; ∃ ι : BialgHom k D H, (∀ d : D, ι d = (d : H)) ∧ ∀ d : D, ((HopfAlgebra.antipode k d : D) : H) = HopfAlgebra.antipode k (d : H))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
