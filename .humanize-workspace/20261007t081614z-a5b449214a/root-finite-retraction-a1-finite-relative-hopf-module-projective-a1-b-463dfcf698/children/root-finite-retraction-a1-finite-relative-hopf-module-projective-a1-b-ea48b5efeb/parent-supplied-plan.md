# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.twisted_presentation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-b-ea48b5efeb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1`
- Child key: `twisted_presentation`
- Declaration: `Submission.p05_fr_rhm_bcsi_twisted_presentation_a5b449214a`
- Exact Lean type: `∀ {S : Type*} [CommRing S] {L : Type*} [AddCommGroup L] [Module S L] (n p : ℕ) (P : Matrix (Fin n) (Fin p) S) (q : (Fin n → S) →ₗ[S] L) (_hq : Function.Surjective q) (_hker : LinearMap.ker q = LinearMap.range P.mulVecLin) (θ : S ≃+* S) (T : L ≃+ L) (_hT : ∀ (s : S) (x : L), T (s • x) = θ s • T x), ∃ qθ : (Fin n → S) →ₗ[S] L, (∀ b : Fin n → S, qθ b = T (q (fun i => θ.symm (b i)))) ∧ Function.Surjective qθ ∧ LinearMap.ker qθ = LinearMap.range (P.map θ.toRingHom).mulVecLin`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
