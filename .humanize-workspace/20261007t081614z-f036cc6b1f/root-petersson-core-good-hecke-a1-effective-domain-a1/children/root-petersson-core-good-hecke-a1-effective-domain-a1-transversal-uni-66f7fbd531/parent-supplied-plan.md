# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.effective_domain-a1.transversal_unique_mod_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-transversal-uni-66f7fbd531/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.effective_domain-a1`
- Child key: `transversal_unique_mod_sign`
- Declaration: `Submission.f036cc6b1f_pc_ed_transversal_unique`
- Exact Lean type: `∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)), (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) → ∀ z : UpperHalfPlane, (∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo) → let F : Set UpperHalfPlane := ⋃ r ∈ R, (fun w : UpperHalfPlane => r • w) '' ModularGroup.fd; ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ → δ ∈ Δ → γ • z ∈ F → δ • z ∈ F → δ = γ ∨ δ = -γ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
