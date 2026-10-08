# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.translation_orbits-a1.cusp_count_factorization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-translation-orbits-a1-cusp-count-factorization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.translation_orbits-a1`
- Child key: `cusp_count_factorization`
- Declaration: `Submission.p10_17ae7b7d_to_cusp_count_factorization`
- Exact Lean type: `∀ (N : ℕ) [NeZero N], ModularCurve.cuspCount N = N.primeFactors.prod (fun p => (Finset.range (N.factorization p + 1)).sum (fun j => Nat.totient (p ^ min j (N.factorization p - j))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
