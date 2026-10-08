# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-cohomology-transfer-a1-restricted-sta-60221840b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1`
- Child key: `prism_boundary_identity`
- Declaration: `Submission.p04_prism_a8325b9888_boundary_identity`
- Exact Lean type: `∀ {k X : Type _} [CommRing k] (u v : X → X), let P : ∀ n : ℕ, (Fin (n + 1) → X) → MonoidAlgebra k (Fin (n + 2) → X) := fun n c => ∑ j : Fin (n + 1), MonoidAlgebra.single (Fin.insertNth j.castSucc (u (c j)) (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i))) ((-1 : k) ^ j.val); (∀ c : Fin 1 → X, Rep.standardComplex.d k X 1 (P 0 c) = MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k)) ∧ ∀ (n : ℕ) (c : Fin (n + 2) → X), Rep.standardComplex.d k X (n + 2) (P (n + 1) c) + ∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove) = MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
