# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curve_ring_equiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-curve-ring-equiv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `curve_ring_equiv`
- Declaration: `Submission.p07_curve_ring_equiv_857cd4d38c`
- Exact Lean type: `∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ) (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U) (D : CerednikDrinfeld.QM.FakeEllipticCurve Λ N U), ∃ (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N T) (i : CategoryTheory.Iso D.A E.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.toRingHom E D i.hom ∧ CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.symm.toRingHom D E i.inv`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
