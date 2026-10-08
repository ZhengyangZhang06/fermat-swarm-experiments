# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-odd-division-detection-a1-odd-prepsi-torsion-a1-torsion-eds-iden-3b3e2390b2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1`
- Child key: `torsion_eds_identification`
- Declaration: `Submission.p03_torsion_eds_identification_68cf3476_d2`
- Exact Lean type: `∀ (k : Type) [Field k] [CharZero k] [DecidableEq k] (W : WeierstrassCurve k), let q := WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine; let h := q W.ψ₂; ∀ f : ℕ → W.toAffine.CoordinateRing, (f 0 = 0 ∧ f 1 = 1 ∧ f 2 = h ∧ f 3 = q (Polynomial.C W.Ψ₃) ∧ f 4 = h * q (Polynomial.C W.preΨ₄) ∧ (∀ r : ℕ, 2 ≤ r → f (2 * r + 1) = f (r + 2) * f r ^ 3 - f (r - 1) * f (r + 1) ^ 3) ∧ (∀ r : ℕ, 3 ≤ r → h * f (2 * r) = f r * (f (r + 2) * f (r - 1) ^ 2 - f (r - 2) * f (r + 1) ^ 2))) → ∀ n : ℕ, f n = q (Polynomial.C (W.preΨ' n)) * (if Even n then h else 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
