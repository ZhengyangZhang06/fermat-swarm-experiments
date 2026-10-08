# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rank_one_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-rank-one-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `rank_one_transfer`
- Declaration: `Submission.p08_7d1ff633a4_rank_one_transfer`
- Exact Lean type: `∀ {k V W : Type} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (n : k) (hn : n ≠ 0) (R : V →ₗ[k] W) (C : W →ₗ[k] V), (∀ v : V, C (R v) = n • v) → Module.finrank k W = 1 → ∀ ℓ : V →ₗ[k] k, Function.Surjective ℓ → Function.Bijective (ℓ.comp C)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
