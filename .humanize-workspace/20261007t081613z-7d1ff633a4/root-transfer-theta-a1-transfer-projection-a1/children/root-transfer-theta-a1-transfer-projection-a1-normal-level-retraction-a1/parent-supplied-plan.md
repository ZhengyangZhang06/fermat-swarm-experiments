# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.transfer_theta-a1.transfer_projection-a1.normal_level_retraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-transfer-theta-a1-transfer-projection-a1-normal-level-retraction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.transfer_theta-a1.transfer_projection-a1`
- Child key: `normal_level_retraction`
- Declaration: `Submission.p08_7d1ff633a4_tp26_normal_level_retraction`
- Exact Lean type: `∀ {G : Type} [Group G] (H : Subgroup G), ∃ a : G → H, (∀ h : H, a (h : G) = h) ∧ (∀ (h : H) (g : G), a ((h : G) * g) = h * a g) ∧ (∀ K : Subgroup G, K.Normal → K ≤ H → ∀ g u : G, u ∈ K → (a g : G)⁻¹ * (a (g * u) : G) ∈ K)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
