# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.transfer_theta-a1.normal_kernel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-transfer-theta-a1-normal-kernel-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.transfer_theta-a1`
- Child key: `normal_kernel`
- Declaration: `Submission.p08_7d1ff633a4_tt26_normal_kernel`
- Exact Lean type: `∀ {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (E : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E → Normal ℚ E → (E.fixingSubgroup.comap r).Normal ∧ (E.fixingSubgroup.comap r).FiniteIndex`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
