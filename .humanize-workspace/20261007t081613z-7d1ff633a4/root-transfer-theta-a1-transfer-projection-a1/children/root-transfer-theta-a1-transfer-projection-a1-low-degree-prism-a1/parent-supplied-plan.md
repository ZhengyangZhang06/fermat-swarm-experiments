# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.transfer_theta-a1.transfer_projection-a1.low_degree_prism-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-transfer-theta-a1-transfer-projection-a1-low-degree-prism-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.transfer_theta-a1.transfer_projection-a1`
- Child key: `low_degree_prism`
- Declaration: `Submission.p08_7d1ff633a4_tp26_low_degree_prism`
- Exact Lean type: `∀ {X V : Type} [AddCommGroup V] (α β : X → X), (∀ F : X → X → V, (∀ x y z : X, F y z - F x z + F x y = 0) → ∀ x y : X, F (β x) (β y) - F (α x) (α y) = F (α y) (β y) - F (α x) (β x)) ∧ (∀ F : X → X → X → V, (∀ w x y z : X, F x y z - F w y z + F w x z - F w x y = 0) → let h : X → X → V := fun x y => F (α x) (β x) (β y) - F (α x) (α y) (β y); ∀ x y z : X, F (β x) (β y) (β z) - F (α x) (α y) (α z) = h y z - h x z + h x y)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
