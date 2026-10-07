# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1.localized_series_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-05d02206d7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1`
- Child key: `localized_series_sum`
- Declaration: `Submission.p06_9e0f5043ff_llm_localized_series_sum`
- Exact Lean type: `∀ (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M] (T : Submonoid B) (s : CompositionSeries (Submodule B M)), s.head = ⊥ → s.last = ⊤ → Module.length (Localization T) (LocalizedModule T M) = Finset.sum Finset.univ (fun i : Fin s.length => Module.length (Localization T) (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
