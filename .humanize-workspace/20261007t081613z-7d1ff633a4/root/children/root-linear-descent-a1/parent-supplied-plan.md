# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.linear_descent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-linear-descent-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `linear_descent`
- Declaration: `Submission.p08_7d1ff633a4_linear_descent`
- Exact Lean type: `∀ {k X Y X' Y' : Type} [Field k] [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] [AddCommGroup X'] [Module k X'] [AddCommGroup Y'] [Module k Y'] (n : k) (hn : n ≠ 0) (R_X : X →ₗ[k] X') (C_X : X' →ₗ[k] X) (R_Y : Y →ₗ[k] Y') (C_Y : Y' →ₗ[k] Y) (Θ : X →ₗ[k] Module.Dual k Y) (Θ' : X' →ₗ[k] Module.Dual k Y'), (∀ x : X, C_X (R_X x) = n • x) → (∀ y : Y, C_Y (R_Y y) = n • y) → (∀ (x : X) (y' : Y'), Θ' (R_X x) y' = Θ x (C_Y y')) → (∀ (x' : X') (y : Y), Θ' x' (R_Y y) = Θ (C_X x') y) → Function.Bijective Θ' → Function.Bijective Θ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
