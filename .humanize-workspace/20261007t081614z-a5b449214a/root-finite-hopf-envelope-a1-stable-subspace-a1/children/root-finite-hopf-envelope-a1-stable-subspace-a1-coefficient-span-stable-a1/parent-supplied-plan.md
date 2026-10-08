# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_hopf_envelope-a1.stable_subspace-a1.coefficient_span_stable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-hopf-envelope-a1-stable-subspace-a1-coefficient-span-stable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_hopf_envelope-a1.stable_subspace-a1`
- Child key: `coefficient_span_stable`
- Declaration: `Submission.p05_fhess_coefficient_span_stable_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C] (x : C) (n : ℕ) (v w : Fin n → C), LinearIndependent k w → Coalgebra.comul (R := k) x = (∑ i : Fin n, TensorProduct.tmul k (v i) (w i)) → FiniteDimensional k (Submodule.span k (Set.range v)) ∧ x ∈ Submodule.span k (Set.range v) ∧ ∀ y ∈ Submodule.span k (Set.range v), Coalgebra.comul (R := k) y ∈ Submodule.span k {t : TensorProduct k C C | ∃ a ∈ Submodule.span k (Set.range v), ∃ b : C, t = TensorProduct.tmul k a b}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
