# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.adic_character_lift-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-adic-character-lift-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `adic_character_lift`
- Declaration: `Submission.p09_af497904fe_adic_character_lift`
- Exact Lean type: `∀ {C G : Type} [CommRing C] [Group G] (J : Ideal C) [IsAdicComplete J C] (a : ℕ → G → C), (∀ (n m : ℕ), n ≤ m → ∀ g : G, a m g - a n g ∈ J ^ n) → (∀ n : ℕ, a n 1 - 1 ∈ J ^ n) → (∀ (n : ℕ) (g h : G), a n (g * h) - a n g * a n h ∈ J ^ n) → ∃! b : G →* Cˣ, ∀ (n : ℕ) (g : G), (b g : C) - a n g ∈ J ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
