# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `petersson_core_good_hecke`
- Declaration: `Submission.f036cc6b1f_petersson_core`
- Exact Lean type: `∀ (M : ℕ) [NeZero M], ∃ B : InnerProductSpace.Core ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2), ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) (f g : CuspForm (CongruenceSubgroup.Gamma0 M) 2), B.inner (CuspForm.heckeTLin 2 hp hpM f) g = B.inner f (CuspForm.heckeTLin 2 hp hpM g)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
