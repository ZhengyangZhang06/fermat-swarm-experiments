# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.coideal_ideal_dichotomy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-coideal-ideal-dichotomy-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1`
- Child key: `coideal_ideal_dichotomy`
- Declaration: `Submission.p05_fr_coideal_ideal_dichotomy_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A] (J : Ideal A) (_hJ : ∀ x ∈ J, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k A A | ∃ a ∈ J, ∃ b : A, t = TensorProduct.tmul k a b}), J = ⊥ ∨ J = ⊤`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
