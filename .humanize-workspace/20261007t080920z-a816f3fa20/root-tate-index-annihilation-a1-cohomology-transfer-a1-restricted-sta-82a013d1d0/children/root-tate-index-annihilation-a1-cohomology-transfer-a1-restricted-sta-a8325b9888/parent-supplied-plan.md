# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-cohomology-transfer-a1-restricted-sta-a8325b9888/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1`
- Child key: `equivariant_prism_homotopy`
- Declaration: `Submission.p04_rsh_82a013d1d0_prism_homotopy`
- Exact Lean type: `∀ {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) (u v : G → G), (∀ (h : H) (g : G), u ((h : G) * g) = (h : G) * u g) → (∀ (h : H) (g : G), v ((h : G) * g) = (h : G) * v g) → let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.standardComplex k G); ∀ U V : CategoryTheory.End C, (∀ (n : ℕ) (c : Fin (n + 1) → G), (U.f n).hom (MonoidAlgebra.single c (1 : k)) = MonoidAlgebra.single (u ∘ c) (1 : k)) → (∀ (n : ℕ) (c : Fin (n + 1) → G), (V.f n).hom (MonoidAlgebra.single c (1 : k)) = MonoidAlgebra.single (v ∘ c) (1 : k)) → Nonempty (Homotopy V U)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
