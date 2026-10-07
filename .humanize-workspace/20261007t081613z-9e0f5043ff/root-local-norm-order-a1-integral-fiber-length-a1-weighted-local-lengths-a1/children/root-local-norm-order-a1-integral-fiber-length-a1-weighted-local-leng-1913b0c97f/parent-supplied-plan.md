# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.length_sum_factors-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-1913b0c97f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1`
- Child key: `length_sum_factors`
- Declaration: `Submission.p06_9e0f5043ff_wll_length_sum_factors`
- Exact Lean type: `∀ (A B M : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] (s : CompositionSeries (Submodule B M)) (p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B), s.head = ⊥ → s.last = ⊤ → (∀ i : Fin s.length, Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B] (B ⧸ (p i).asIdeal))) → Module.length A M = Finset.sum Finset.univ (fun i : Fin s.length => Module.length A (B ⧸ (p i).asIdeal))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
