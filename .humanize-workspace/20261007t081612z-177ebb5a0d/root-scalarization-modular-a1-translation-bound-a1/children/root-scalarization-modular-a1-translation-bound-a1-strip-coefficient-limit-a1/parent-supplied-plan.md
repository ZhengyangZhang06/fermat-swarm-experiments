# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-translation-bound-a1-strip-coefficient-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.translation_bound-a1`
- Child key: `strip_coefficient_limit`
- Declaration: `Submission.p02_es_177ebb5a_tb_strip_coefficient_limit`
- Exact Lean type: `∀ (n : ℕ) (u : UpperHalfPlane → ℂ) (G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (a C Y L : ℝ), 0 < a → 0 ≤ C → 0 ≤ L → Continuous u → HeckeEis.IsEichlerIntegral n u G → (∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖u τ‖ ≤ C * Real.exp (-a * τ.im)) → ∃ (A : ↥(HeckeEis.BinaryForm ℂ n)) (K : ℝ), 0 ≤ K ∧ ∀ τ : UpperHalfPlane, 0 ≤ τ.re → τ.re ≤ L → max 1 Y ≤ τ.im → ∀ d : Fin 2 →₀ ℕ, ‖MvPolynomial.coeff d ((G τ).val - A.val)‖ ≤ K * (1 + τ.im) ^ n * Real.exp (-a * τ.im)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
