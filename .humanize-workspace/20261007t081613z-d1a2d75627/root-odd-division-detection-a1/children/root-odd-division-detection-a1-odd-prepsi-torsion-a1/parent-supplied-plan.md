# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.odd_division_detection-a1.odd_prepsi_torsion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-odd-division-detection-a1-odd-prepsi-torsion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.odd_division_detection-a1`
- Child key: `odd_prepsi_torsion`
- Declaration: `Submission.p03_odd_prepsi_torsion_68cf3476`
- Exact Lean type: `∀ (F : Type) [Field F] [CharZero F] [DecidableEq F] (W : WeierstrassCurve F), W.Δ ≠ 0 → ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (x y : F) (h : W.toAffine.Nonsingular x y), n • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ (W.preΨ' n).eval x = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
