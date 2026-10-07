# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.central_telescoping-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-cohomology-transfer-a1-restricted-sta-b34131935c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1`
- Child key: `central_telescoping`
- Declaration: `Submission.p04_pb_60221840b0_central_telescoping`
- Exact Lean type: `∀ {k X : Type _} [CommRing k] (u v : X → X) (m : ℕ) (c : Fin (m + 1) → X), let Q : Fin (m + 1) → (Fin (m + 2) → X) := fun j => Fin.insertNth j.castSucc (u (c j)) (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i)); (∑ j : Fin (m + 1), (MonoidAlgebra.single (Q j ∘ j.castSucc.succAbove) (1 : k) - MonoidAlgebra.single (Q j ∘ j.succ.succAbove) (1 : k))) = MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
