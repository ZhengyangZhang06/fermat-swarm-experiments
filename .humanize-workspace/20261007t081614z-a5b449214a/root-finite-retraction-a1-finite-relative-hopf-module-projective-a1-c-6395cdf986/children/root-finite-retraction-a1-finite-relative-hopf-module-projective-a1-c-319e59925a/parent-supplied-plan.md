# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1.algebra_coaction_twist-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-c-319e59925a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1`
- Child key: `algebra_coaction_twist`
- Declaration: `Submission.p05_ct_algebra_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A] {H : Type*} [CommRing H] [HopfAlgebra k H] (ι : BialgHom k A H), ∃ θ : TensorProduct k A H ≃ₐ[k] TensorProduct k A H, ∀ (a : A) (h : H), θ (TensorProduct.tmul k a h) = (TensorProduct.map (LinearMap.id : A →ₗ[k] A) ι.toLinearMap) (Coalgebra.comul (R := k) a) * TensorProduct.tmul k (1 : A) h`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
