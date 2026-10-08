# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.base_changed_presentation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-b-8cb85f43c4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1`
- Child key: `base_changed_presentation`
- Declaration: `Submission.p05_fr_rhm_bcsi_base_changed_presentation_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {M : Type*} [AddCommGroup M] [Module R M] (n p : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M) (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin), ∃ q : (Fin n → S) →ₗ[S] TensorProduct R S M, (∀ b : Fin n → S, q b = ∑ i, b i • TensorProduct.tmul R (1 : S) (π (Pi.single i (1 : R)))) ∧ Function.Surjective q ∧ LinearMap.ker q = LinearMap.range (P.map (algebraMap R S)).mulVecLin`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
