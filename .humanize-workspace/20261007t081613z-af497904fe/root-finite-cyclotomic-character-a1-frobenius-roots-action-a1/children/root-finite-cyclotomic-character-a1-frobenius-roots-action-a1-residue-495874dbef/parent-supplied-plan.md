# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_cyclotomic_character-a1.frobenius_roots_action-a1.residue_injective-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-finite-cyclotomic-character-a1-frobenius-roots-action-a1-residue-495874dbef/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_cyclotomic_character-a1.frobenius_roots_action-a1`
- Child key: `residue_injective`
- Declaration: `Submission.p09_af497904fe_fcc_fra_residue_injective`
- Exact Lean type: `∀ (N : ℕ) [NeZero N] (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ → ∀ x y : P, x ^ N = 1 → y ^ N = 1 → IsLocalRing.residue P x = IsLocalRing.residue P y → x = y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
