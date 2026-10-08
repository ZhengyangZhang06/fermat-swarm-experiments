# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-5b68ec51cc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.projective_of_trivial_minors-a1`
- Child key: `unit_minor_splitting`
- Declaration: `Submission.p05_ptm_split_of_unit_minor_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (n p d : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M) (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin) (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p) (_hunit : IsUnit (Matrix.det (P.submatrix rows cols))) (_hnext : ∀ (rows' : Fin (d + 1) ↪ Fin n) (cols' : Fin (d + 1) ↪ Fin p), Matrix.det (P.submatrix rows' cols') = 0), ∃ s : M →ₗ[R] (Fin n → R), π.comp s = LinearMap.id`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
