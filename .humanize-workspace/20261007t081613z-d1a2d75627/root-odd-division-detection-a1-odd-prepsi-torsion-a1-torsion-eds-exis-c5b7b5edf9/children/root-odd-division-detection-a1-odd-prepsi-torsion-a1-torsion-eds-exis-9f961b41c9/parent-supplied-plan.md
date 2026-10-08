# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1.finite_kernel_of_nsmul_nonzero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-odd-division-detection-a1-odd-prepsi-torsion-a1-torsion-eds-exis-9f961b41c9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1`
- Child key: `finite_kernel_of_nsmul_nonzero`
- Declaration: `Submission.p03_ptf_finite_kernel_of_nsmul_nonzero_c5b7b5ed_d6`
- Exact Lean type: `∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k), W.Δ ≠ 0 → ∀ n : ℕ, (∃ P : W.toAffine.Point, n • P ≠ 0) → Finite {P : W.toAffine.Point // n • P = 0}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
