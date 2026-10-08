# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.section_of_inner_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-6f95d067f1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1`
- Child key: `section_of_inner_inverse`
- Declaration: `Submission.p05_ums_section_of_inner_inverse_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] {F : Type*} [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G] {M : Type*} [AddCommGroup M] [Module R M] (f : G →ₗ[R] F) (g : F →ₗ[R] G) (π : F →ₗ[R] M) (_hinner : (f.comp g).comp f = f) (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range f), ∃ s : M →ₗ[R] F, π.comp s = LinearMap.id`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
