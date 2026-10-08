# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1.left_level_boundary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-transfer-theta-a1-cup-pairings-a1-cup-one-one-a1-left-level-boundary-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1`
- Child key: `left_level_boundary`
- Declaration: `Submission.p08_7d1ff633a4_cp11_left_level_boundary`
- Exact Lean type: `∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (a : A) (g : groupCohomology.cocycles₁ B), groupCohomology.IsLevelConstant₁ r (⇑g) → groupCohomology.cupCochain φ (fun s : G => A.ρ s a - a) (⇑g) ∈ groupCohomology.levelCoboundaries₂ r N`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
