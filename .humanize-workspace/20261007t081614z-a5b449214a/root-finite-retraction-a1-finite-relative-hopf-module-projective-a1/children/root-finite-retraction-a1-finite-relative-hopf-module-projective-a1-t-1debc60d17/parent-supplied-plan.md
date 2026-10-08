# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.tensor_ideal_descent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-t-1debc60d17/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1`
- Child key: `tensor_ideal_descent`
- Declaration: `Submission.p05_fr_rhm_tensor_ideal_descent_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] {H : Type*} [CommRing H] [Algebra k H] (f : A →ₗ[k] H) (_hf : Function.Injective f) (J : Ideal A) (t : TensorProduct k A A) (_ht : TensorProduct.map (LinearMap.id : A →ₗ[k] A) f t ∈ Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A H).toRingHom J), t ∈ Submodule.span k {z : TensorProduct k A A | ∃ a ∈ J, ∃ b : A, z = TensorProduct.tmul k a b}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
