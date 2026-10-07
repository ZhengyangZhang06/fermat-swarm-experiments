# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rigidification_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-rigidification-reduction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `rigidification_reduction`
- Declaration: `Submission.p07_rigidification_reduction_857cd4d38c`
- Exact Lean type: `∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (r N : ℕ) (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (A₀ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (S : Type) [CommRing S] [Algebra 𝒪 S] (ψ : Onr →ₐ[𝒪] S) (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) (V : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (S ⧸ Ideal.span {algebraMap 𝒪 S π})) (g : Quiver.Hom V.A E.A) (hg : CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 S π})) E V g) (σ : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification r π A₀ ((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 S π})).comp ψ) V), ∃ ρ : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification r π A₀ ψ E, ρ.d = σ.d ∧ CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.IsPullbackVia (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 S π})) g hg ρ σ`

## Sibling prerequisites

- `root.curve_ring_equiv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
