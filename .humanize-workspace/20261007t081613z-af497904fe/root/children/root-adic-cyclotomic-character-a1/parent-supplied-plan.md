# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.adic_cyclotomic_character-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-adic-cyclotomic-character-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `adic_cyclotomic_character`
- Declaration: `Submission.p09_af497904fe_adic_cyclotomic_character`
- Exact Lean type: `∀ {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪] (p : ℕ) [Fact p.Prime], (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪 → ∀ {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R], IsLocalHom (algebraMap 𝒪 R) → ∃ c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ, (∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ x ∈ F, σ x = τ x) → ((c σ : Rˣ) : R) - ((c τ : Rˣ) : R) ∈ IsLocalRing.maximalIdeal R ^ n) ∧ (∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ → ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), P.IsFrobeniusAt σ ℓ → ((c σ : Rˣ) : R) = (ℓ : R))`

## Sibling prerequisites

- `root.finite_cyclotomic_character-a1`
- `root.adic_character_lift-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
