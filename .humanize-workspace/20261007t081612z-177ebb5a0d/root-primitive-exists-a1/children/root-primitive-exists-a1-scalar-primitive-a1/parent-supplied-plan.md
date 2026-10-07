# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_exists-a1.scalar_primitive-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-scalar-primitive-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_exists-a1`
- Child key: `scalar_primitive`
- Declaration: `Submission.p02_es_177ebb5a_primitive_exists_scalar_primitive`
- Exact Lean type: `∀ (a : ℂ → ℂ), DifferentiableOn ℂ a {z : ℂ | 0 < z.im} → ∃ A : ℂ → ℂ, ∀ z : ℂ, 0 < z.im → HasDerivAt A (a z) z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
