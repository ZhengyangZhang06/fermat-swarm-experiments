# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-hecke-integral-adjointness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1`
- Child key: `hecke_integral_adjointness`
- Declaration: `Submission.f036cc6b1f_pc_hecke_integral`
- Exact Lean type: `∀ (M : ℕ) [NeZero M] (F : Set UpperHalfPlane), MeasurableSet F → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ (CongruenceSubgroup.Gamma0 M) ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ (CongruenceSubgroup.Gamma0 M) → δ • z ∈ F → δ = γ ∨ δ = -γ) → ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) (f g : CuspForm (CongruenceSubgroup.Gamma0 M) 2), MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F) (UpperHalfPlane.petersson 2 (CuspForm.heckeTLin 2 hp hpM f) g) = MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F) (UpperHalfPlane.petersson 2 f (CuspForm.heckeTLin 2 hp hpM g))`

## Sibling prerequisites

- `root.petersson_core_good_hecke-a1.petersson_integral_core-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
