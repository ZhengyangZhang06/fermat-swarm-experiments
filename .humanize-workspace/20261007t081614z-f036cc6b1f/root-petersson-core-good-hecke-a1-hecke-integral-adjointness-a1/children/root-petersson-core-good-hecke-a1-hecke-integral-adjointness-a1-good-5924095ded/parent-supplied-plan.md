# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-hecke-integral-adjointness-a1-good-5924095ded/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1`
- Child key: `good_prime_transversal`
- Declaration: `Submission.f036cc6b1f_pc_hi_good_prime_transversal`
- Exact Lean type: `∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → ¬ p ∣ M → ∃ r : Fin (p + 1) → Matrix.SpecialLinearGroup (Fin 2) ℤ, (∀ i, r i ∈ CongruenceSubgroup.Gamma0 M) ∧ (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma0 M → ∃! i : Fin (p + 1), (p : ℤ) ∣ (γ * (r i)⁻¹) 0 1) ∧ (∀ i : Fin p, ModularForm.heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ (r i.castSucc) = ModularForm.heckeMatrix p i.val) ∧ (∃ β : Matrix.SpecialLinearGroup (Fin 2) ℤ, β ∈ CongruenceSubgroup.Gamma0 M ∧ ModularForm.heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ (r (Fin.last p)) = Matrix.SpecialLinearGroup.mapGL ℝ β * ModularForm.heckeDiagMatrix p)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
