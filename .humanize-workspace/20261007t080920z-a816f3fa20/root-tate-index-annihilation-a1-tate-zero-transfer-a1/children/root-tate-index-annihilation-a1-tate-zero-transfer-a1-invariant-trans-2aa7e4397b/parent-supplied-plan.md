# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.tate_zero_transfer-a1.invariant_transfer_norm_index-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-tate-zero-transfer-a1-invariant-trans-2aa7e4397b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1`
- Child key: `invariant_transfer_norm_index`
- Declaration: `Submission.p04_tz91_invariant_transfer_norm_index`
- Exact Lean type: `∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H], ∃ c : (Rep.res H.subtype A).ρ.invariants →ₗ[k] A.ρ.invariants, (∀ v : A, c ((Rep.res H.subtype A).ρ.normToInvariants v) = A.ρ.normToInvariants v) ∧ ∀ (a : A.ρ.invariants) (b : (Rep.res H.subtype A).ρ.invariants), (b : A) = (a : A) → c b = H.index • a`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
