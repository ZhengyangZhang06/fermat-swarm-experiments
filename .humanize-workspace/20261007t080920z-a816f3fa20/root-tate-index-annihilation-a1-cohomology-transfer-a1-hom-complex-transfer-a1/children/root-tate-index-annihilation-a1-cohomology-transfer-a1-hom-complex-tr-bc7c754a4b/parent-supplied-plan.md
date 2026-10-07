# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-cohomology-transfer-a1-hom-complex-tr-bc7c754a4b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1`
- Child key: `hom_coset_average_exists`
- Declaration: `Submission.p04_hct139_coset_average_exists`
- Exact Lean type: `∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A B : Rep k G) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)], ∃ C : (Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) →ₗ[k] (Quiver.Hom B A), ∀ (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (x : B), (C F).hom x = ∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
