# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.translation_bound-a1.periodic_strip_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-translation-bound-a1-periodic-strip-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.translation_bound-a1`
- Child key: `periodic_strip_bound`
- Declaration: `Submission.p02_es_177ebb5a_tb_periodic_strip_bound`
- Exact Lean type: `∀ (N : ℕ) [NeZero N] (q : UpperHalfPlane → ℂ), (∀ τ : UpperHalfPlane, q ((ModularGroup.T ^ N) • τ) = q τ) → (∃ M Y : ℝ, ∀ τ : UpperHalfPlane, 0 ≤ τ.re → τ.re ≤ (N : ℝ) → Y ≤ τ.im → ‖q τ‖ ≤ M) → UpperHalfPlane.IsBoundedAtImInfty q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
