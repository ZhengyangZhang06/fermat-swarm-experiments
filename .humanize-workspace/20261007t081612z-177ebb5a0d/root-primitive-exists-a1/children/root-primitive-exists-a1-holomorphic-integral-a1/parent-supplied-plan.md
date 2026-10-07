# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_exists-a1.holomorphic_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-holomorphic-integral-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_exists-a1`
- Child key: `holomorphic_integral`
- Declaration: `Submission.p02_es_177ebb5a_primitive_exists_holomorphic_integral`
- Exact Lean type: `∀ (n : ℕ) (h : UpperHalfPlane → ℂ), DifferentiableOn ℂ (fun z : ℂ => h (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} → ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n), HeckeEis.IsEichlerIntegral n h F`

## Sibling prerequisites

- `root.primitive_exists-a1.scalar_primitive-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
