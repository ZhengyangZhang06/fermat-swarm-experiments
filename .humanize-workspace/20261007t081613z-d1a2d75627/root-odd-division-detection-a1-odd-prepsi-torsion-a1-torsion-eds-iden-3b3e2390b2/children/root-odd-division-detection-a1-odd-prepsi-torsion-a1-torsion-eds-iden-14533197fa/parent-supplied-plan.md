# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.eds_recurrence_uniqueness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-odd-division-detection-a1-odd-prepsi-torsion-a1-torsion-eds-iden-14533197fa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1`
- Child key: `eds_recurrence_uniqueness`
- Declaration: `Submission.p03_eds_recurrence_unique_68cf3476_d3`
- Exact Lean type: `∀ (R : Type) [CommRing R] [IsDomain R] (h : R), h ≠ 0 → ∀ f g : ℕ → R, (∀ n : ℕ, n ≤ 4 → f n = g n) → (∀ r : ℕ, 2 ≤ r → f (2 * r + 1) = f (r + 2) * f r ^ 3 - f (r - 1) * f (r + 1) ^ 3) → (∀ r : ℕ, 3 ≤ r → h * f (2 * r) = f r * (f (r + 2) * f (r - 1) ^ 2 - f (r - 2) * f (r + 1) ^ 2)) → (∀ r : ℕ, 2 ≤ r → g (2 * r + 1) = g (r + 2) * g r ^ 3 - g (r - 1) * g (r + 1) ^ 3) → (∀ r : ℕ, 3 ≤ r → h * g (2 * r) = g r * (g (r + 2) * g (r - 1) ^ 2 - g (r - 2) * g (r + 1) ^ 2)) → ∀ n : ℕ, f n = g n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
