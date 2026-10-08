# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.canonical_eds_recurrences-a1.canonical_even_recurrence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-odd-division-detection-a1-odd-prepsi-torsion-a1-torsion-eds-iden-3faa1ad688/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.canonical_eds_recurrences-a1`
- Child key: `canonical_even_recurrence`
- Declaration: `Submission.p03_eds_canonical_even_recurrence_68cf3476_d4`
- Exact Lean type: `∀ (k : Type) [Field k] [CharZero k] [DecidableEq k] (W : WeierstrassCurve k), let q := WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine; let h := q W.ψ₂; let F : ℕ → W.toAffine.CoordinateRing := fun n => q (Polynomial.C (W.preΨ' n)) * (if Even n then h else 1); ∀ r : ℕ, 3 ≤ r → h * F (2 * r) = F r * (F (r + 2) * F (r - 1) ^ 2 - F (r - 2) * F (r + 1) ^ 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
