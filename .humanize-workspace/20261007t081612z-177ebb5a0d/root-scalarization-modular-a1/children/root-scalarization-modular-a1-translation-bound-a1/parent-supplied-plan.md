# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.translation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-translation-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1`
- Child key: `translation_bound`
- Declaration: `Submission.p02_es_177ebb5a_sm_translation_bound`
- Exact Lean type: `∀ (N : ℕ) [NeZero N] (n : ℕ) (u : UpperHalfPlane → ℂ) (G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), Continuous u → HeckeEis.IsEichlerIntegral n u G → (∀ τ : UpperHalfPlane, G ((ModularGroup.T ^ N) • τ) = ((HeckeEis.binaryFormRepSL ℂ n) (ModularGroup.T ^ N)) (G τ)) → (∃ (a C Y : ℝ), 0 < a ∧ 0 ≤ C ∧ ∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖u τ‖ ≤ C * Real.exp (-a * τ.im)) → UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (G τ).val)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
