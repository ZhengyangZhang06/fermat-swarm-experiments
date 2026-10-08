# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.transfer_theta-a1.transfer_projection-a1.bilinear_averaging-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-transfer-theta-a1-transfer-projection-a1-bilinear-averaging-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.transfer_theta-a1.transfer_projection-a1`
- Child key: `bilinear_averaging`
- Declaration: `Submission.p08_7d1ff633a4_tp26_bilinear_averaging`
- Exact Lean type: `∀ {k G X Y ι : Type} [Field k] [Group G] [MulAction G X] [MulAction G Y] [Fintype ι] (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (t : ι → G) (F : X → A) (Q : Y → B), ((∀ (s : G) (x : X), F (s • x) = A.ρ s (F x)) → ∀ (x : X) (y : Y), (∑ c : ι, N.ρ (t c) (φ (F ((t c)⁻¹ • x)) (Q ((t c)⁻¹ • y)))) = φ (F x) (∑ c : ι, B.ρ (t c) (Q ((t c)⁻¹ • y)))) ∧ ((∀ (s : G) (y : Y), Q (s • y) = B.ρ s (Q y)) → ∀ (x : X) (y : Y), (∑ c : ι, N.ρ (t c) (φ (F ((t c)⁻¹ • x)) (Q ((t c)⁻¹ • y)))) = φ (∑ c : ι, A.ρ (t c) (F ((t c)⁻¹ • x))) (Q y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
