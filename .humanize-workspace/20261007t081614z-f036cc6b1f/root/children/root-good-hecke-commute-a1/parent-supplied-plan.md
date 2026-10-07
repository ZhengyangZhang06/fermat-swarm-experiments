# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.good_hecke_commute-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-good-hecke-commute-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `good_hecke_commute`
- Declaration: `Submission.f036cc6b1f_hecke_commute`
- Exact Lean type: `∀ (M : ℕ) [NeZero M] (p r : ℕ) (hp : p.Prime) (hr : r.Prime) (hpM : ¬ p ∣ M) (hrM : ¬ r ∣ M), (CuspForm.heckeTLin 2 hp hpM).comp (CuspForm.heckeTLin 2 hr hrM) = (CuspForm.heckeTLin 2 hr hrM).comp (CuspForm.heckeTLin 2 hp hpM)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
