# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-04a817ef67/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1`
- Child key: `local_length_multiplicity`
- Declaration: `Submission.p06_9e0f5043ff_wll_local_length_multiplicity`
- Exact Lean type: `∀ (B : Type*) [CommRing B] [IsDedekindDomain B] (b : B) (s : CompositionSeries (Submodule B (B ⧸ Ideal.span ({b} : Set B)))) (p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B), s.head = ⊥ → s.last = ⊤ → (∀ i : Fin s.length, Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B] (B ⧸ (p i).asIdeal))) → ∀ q : IsDedekindDomain.HeightOneSpectrum B, Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⧸ Ideal.span ({algebraMap B (Localization.AtPrime q.asIdeal) b} : Set (Localization.AtPrime q.asIdeal))) = (Nat.card {i : Fin s.length // p i = q} : ℕ∞)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
