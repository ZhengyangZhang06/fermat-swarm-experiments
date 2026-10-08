# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1.coprime_orbit_product-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-translation-orbits-a1-coprime-count-mul-a-af6066755c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1`
- Child key: `coprime_orbit_product`
- Declaration: `Submission.p10_17ae7b7d_ccm_coprime_orbit_product`
- Exact Lean type: `∀ (G X Y : Type) [Group G] [MulAction G X] [MulAction G Y] (g : G) (m n : ℕ) [NeZero m] [NeZero n], Nat.Coprime m n → (∀ x : X, (g ^ m) • x = x) → (∀ y : Y, (g ^ n) • y = y) → Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (X × Y))) = Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) X)) * Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) Y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
