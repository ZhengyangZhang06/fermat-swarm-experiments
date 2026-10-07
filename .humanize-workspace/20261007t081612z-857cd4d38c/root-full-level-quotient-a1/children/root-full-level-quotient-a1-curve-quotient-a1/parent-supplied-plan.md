# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.full_level_quotient-a1.curve_quotient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1-curve-quotient-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.full_level_quotient-a1`
- Child key: `curve_quotient`
- Declaration: `Submission.p07_flq_curve_quotient_857cd4d38c`
- Exact Lean type: `∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ) (S : Type) [CommRing S] (J : Ideal S) (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S), ∃ (EJ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (S ⧸ J)) (g : Quiver.Hom EJ.A E.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk J) E EJ g`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
