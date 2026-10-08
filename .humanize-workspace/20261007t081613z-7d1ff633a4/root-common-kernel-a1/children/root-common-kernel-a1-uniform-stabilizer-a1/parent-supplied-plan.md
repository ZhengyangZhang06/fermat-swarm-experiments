# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.common_kernel-a1.uniform_stabilizer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-common-kernel-a1-uniform-stabilizer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.common_kernel-a1`
- Child key: `uniform_stabilizer`
- Declaration: `Submission.p08_7d1ff633a4_ck_uniform_stabilizer`
- Exact Lean type: `∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep.{0} k G) [FiniteDimensional k M], (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ g : G, r g ∈ F.fixingSubgroup → M.ρ g m = m) → ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ g : G, r g ∈ F.fixingSubgroup → ∀ m : M, M.ρ g m = m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
