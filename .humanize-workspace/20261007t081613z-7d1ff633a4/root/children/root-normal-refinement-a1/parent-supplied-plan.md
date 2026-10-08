# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.normal_refinement-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-normal-refinement-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `normal_refinement`
- Declaration: `Submission.p08_7d1ff633a4_normal_refinement`
- Exact Lean type: `∀ {ι : Type} [Finite ι] (F : ι → IntermediateField ℚ (AlgebraicClosure ℚ)), (∀ i, FiniteDimensional ℚ (F i)) → ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧ Normal ℚ E ∧ (∀ i, F i ≤ E) ∧ E.fixingSubgroup.Normal ∧ E.fixingSubgroup.FiniteIndex`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
