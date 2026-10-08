# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.trace_congruence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-trace-congruence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `trace_congruence`
- Declaration: `Submission.p09_af497904fe_trace_congruence`
- Exact Lean type: `∀ {C W : Type} [CommRing C] [AddCommGroup W] [Module C W] [Module.Free C W] [Module.Finite C W] (J : Ideal C) (u v : Module.End C W), (∀ w : W, (u - v) w ∈ J • (⊤ : Submodule C W)) → LinearMap.trace C W u - LinearMap.trace C W v ∈ J`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
