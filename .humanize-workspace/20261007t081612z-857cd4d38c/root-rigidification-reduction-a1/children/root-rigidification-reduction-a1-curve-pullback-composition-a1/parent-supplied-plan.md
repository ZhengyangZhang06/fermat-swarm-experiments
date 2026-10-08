# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rigidification_reduction-a1.curve_pullback_composition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-rigidification-reduction-a1-curve-pullback-composition-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rigidification_reduction-a1`
- Child key: `curve_pullback_composition`
- Declaration: `Submission.p07_rr_pullback_comp_857cd4d38c`
- Exact Lean type: `∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ) (S₀ S₁ S₂ : Type) [CommRing S₀] [CommRing S₁] [CommRing S₂] (f : S₀ →+* S₁) (h : S₁ →+* S₂) (E₀ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S₀) (E₁ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S₁) (E₂ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S₂) (g₀₁ : Quiver.Hom E₁.A E₀.A) (g₁₂ : Quiver.Hom E₂.A E₁.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia f E₀ E₁ g₀₁ → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia h E₁ E₂ g₁₂ → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia (h.comp f) E₀ E₂ (CategoryTheory.CategoryStruct.comp g₁₂ g₀₁)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
