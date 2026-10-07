# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.noncentral_cancellation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-cohomology-transfer-a1-restricted-sta-606bdf62ce/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1`
- Child key: `noncentral_cancellation`
- Declaration: `Submission.p04_pb_60221840b0_noncentral_cancellation`
- Exact Lean type: `∀ {k X : Type _} [CommRing k] (u v : X → X) (n : ℕ) (c : Fin (n + 2) → X), let Q : ∀ m : ℕ, (Fin (m + 1) → X) → Fin (m + 1) → (Fin (m + 2) → X) := fun m d j => Fin.insertNth j.castSucc (u (d j)) (fun i : Fin (m + 1) => if i < j then u (d i) else v (d i)); (∑ j : Fin (n + 2), ∑ a : Fin (n + 3) with a.val < j.val ∨ j.val + 1 < a.val, MonoidAlgebra.single (Q (n + 1) c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) + (∑ b : Fin (n + 2), ∑ t : Fin (n + 1), MonoidAlgebra.single (Q n (c ∘ b.succAbove) t) ((-1 : k) ^ (b.val + t.val))) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
