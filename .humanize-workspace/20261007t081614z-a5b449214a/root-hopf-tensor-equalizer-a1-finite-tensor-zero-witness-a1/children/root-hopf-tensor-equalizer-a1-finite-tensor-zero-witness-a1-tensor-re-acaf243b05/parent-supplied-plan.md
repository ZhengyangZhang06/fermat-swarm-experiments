# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.hopf_tensor_equalizer-a1.finite_tensor_zero_witness-a1.tensor_relation_kernel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-finite-tensor-zero-witness-a1-tensor-re-acaf243b05/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.hopf_tensor_equalizer-a1.finite_tensor_zero_witness-a1`
- Child key: `tensor_relation_kernel`
- Declaration: `Submission.p05_ftzw_tensor_relation_kernel_a5b449214a`
- Exact Lean type: `∀ {D : Type*} [CommRing D] {M : Type*} [AddCommGroup M] [Module D M] {P : Type*} [AddCommGroup P] [Module D P], let b : M → P → FreeAbelianGroup (M × P) := fun u z => FreeAbelianGroup.of (u, z); (FreeAbelianGroup.lift (fun x : M × P => TensorProduct.tmul D x.1 x.2)).ker = AddSubgroup.closure {r : FreeAbelianGroup (M × P) | (∃ z : P, r = b 0 z) ∨ (∃ u : M, r = b u 0) ∨ (∃ (u v : M) (z : P), r = b (u + v) z - b u z - b v z) ∨ (∃ (u : M) (z w : P), r = b u (z + w) - b u z - b u w) ∨ (∃ (d : D) (u : M) (z : P), r = b (d • u) z - b u (d • z))}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
