# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1.patch_power_sections-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-principal-c-9e3a59aef9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1`
- Child key: `patch_power_sections`
- Declaration: `Submission.p05_pcs_patch_power_sections_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {F : Type*} [AddCommGroup F] [Module R F] (π : F →ₗ[R] M) (q : ℕ) (f : Fin q → R) (_hcover : Ideal.span (Set.range f) = ⊤) (N : Fin q → ℕ) (_hN : ∀ i, 0 < N i) (t : Fin q → M →ₗ[R] F) (_ht : ∀ i, π.comp (t i) = (f i) ^ (N i) • (LinearMap.id : M →ₗ[R] M)), ∃ s : M →ₗ[R] F, π.comp s = LinearMap.id`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
