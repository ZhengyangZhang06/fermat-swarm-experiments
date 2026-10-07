# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_order_support_ascent-a1.order_zero_from_monic_pair-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1-order-zero-from-monic-pair-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_order_support_ascent-a1`
- Child key: `order_zero_from_monic_pair`
- Declaration: `Submission.p06_9e0f5043ff_fosa_ord_zero_of_monic_pair`
- Exact Lean type: `∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [Algebra.IsIntegral E L] (w : AlgebraicCurve.Place K L) (f : L) (P Q : Polynomial E), f ≠ 0 → P.Monic → Q.Monic → Polynomial.eval₂ (algebraMap E L) f P = 0 → Polynomial.eval₂ (algebraMap E L) (f⁻¹) Q = 0 → (∀ i : ℕ, P.coeff i ∈ (w.restrict E).toValuationSubring) → (∀ i : ℕ, Q.coeff i ∈ (w.restrict E).toValuationSubring) → w.ord f = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
