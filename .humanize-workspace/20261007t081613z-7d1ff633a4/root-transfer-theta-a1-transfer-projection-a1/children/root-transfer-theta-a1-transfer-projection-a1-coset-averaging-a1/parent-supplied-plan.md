# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.transfer_theta-a1.transfer_projection-a1.coset_averaging-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-transfer-theta-a1-transfer-projection-a1-coset-averaging-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.transfer_theta-a1.transfer_projection-a1`
- Child key: `coset_averaging`
- Declaration: `Submission.p08_7d1ff633a4_tp26_coset_averaging`
- Exact Lean type: `∀ {k G X : Type} [Field k] [Group G] [MulAction G X] (H : Subgroup G) [Fintype (G ⧸ H)] (V : Rep.{0} k G) (t : (G ⧸ H) → G), (∀ c : G ⧸ H, (t c : G ⧸ H) = c) → ∃ T : (X → V) →ₗ[k] (X → V), (∀ (F : X → V) (x : X), T F x = ∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x))) ∧ (∀ F : X → V, (∀ (h : H) (x : X), F ((h : G) • x) = V.ρ (h : G) (F x)) → ∀ (s : G) (x : X), T F (s • x) = V.ρ s (T F x)) ∧ (∀ F : X → V, (∀ (s : G) (x : X), F (s • x) = V.ρ s (F x)) → ∀ x : X, T F x = (H.index : k) • F x) ∧ (∀ u : (G ⧸ H) → G, (∀ c : G ⧸ H, (u c : G ⧸ H) = c) → ∀ F : X → V, (∀ (h : H) (x : X), F ((h : G) • x) = V.ρ (h : G) (F x)) → ∀ x : X, T F x = ∑ c : G ⧸ H, V.ρ (u c) (F ((u c)⁻¹ • x)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
