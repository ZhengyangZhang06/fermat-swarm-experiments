# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1.clear_away_section-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-principal-c-45360bbe28/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1`
- Child key: `clear_away_section`
- Declaration: `Submission.p05_pcs_clear_away_section_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (n p : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M) (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin) (f : R) (_hlocal : ∃ σ : LocalizedModule (Submonoid.powers f) M →ₗ[Localization.Away f] LocalizedModule (Submonoid.powers f) (Fin n → R), (LocalizedModule.map (Submonoid.powers f) π).comp σ = LinearMap.id), ∃ N : ℕ, 0 < N ∧ ∃ t : M →ₗ[R] (Fin n → R), π.comp t = f ^ N • (LinearMap.id : M →ₗ[R] M)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
