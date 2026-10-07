# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1.localized_residue_factors-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-d6bfe2e051/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1`
- Child key: `localized_residue_factors`
- Declaration: `Submission.p06_9e0f5043ff_llm_localized_residue_factors`
- Exact Lean type: `∀ (B : Type*) [CommRing B] [IsDedekindDomain B] (p q : IsDedekindDomain.HeightOneSpectrum B), (p = q → IsSimpleModule (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl (B ⧸ p.asIdeal))) ∧ (p ≠ q → Subsingleton (LocalizedModule q.asIdeal.primeCompl (B ⧸ p.asIdeal)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
