# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.residue_composition_series-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-a3d54691b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1`
- Child key: `residue_composition_series`
- Declaration: `Submission.p06_9e0f5043ff_wll_residue_composition_series`
- Exact Lean type: `∀ (A B : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B] (b : B), b ≠ 0 → ∀ n : ℕ, Module.length A (B ⧸ Ideal.span ({b} : Set B)) = (n : ℕ∞) → ∃ s : CompositionSeries (Submodule B (B ⧸ Ideal.span ({b} : Set B))), s.head = ⊥ ∧ s.last = ⊤ ∧ ∃ p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B, ∀ i : Fin s.length, Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B] (B ⧸ (p i).asIdeal))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
