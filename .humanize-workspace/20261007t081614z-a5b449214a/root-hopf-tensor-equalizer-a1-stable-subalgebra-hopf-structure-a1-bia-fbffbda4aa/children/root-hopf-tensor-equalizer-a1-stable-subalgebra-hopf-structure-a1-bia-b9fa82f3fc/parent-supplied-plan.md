# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.bialgebra_restriction-a1.coalgebra_law_descent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1-bia-b9fa82f3fc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.bialgebra_restriction-a1`
- Child key: `coalgebra_law_descent`
- Declaration: `Submission.p05_hte_sshs_br_coalgebra_laws_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C] {V : Type*} [AddCommGroup V] [Module k V] (i : V →ₗ[k] C) (_hi : Function.Injective i) (δ : V →ₗ[k] TensorProduct k V V) (ε : V →ₗ[k] k) (_hδ : ∀ v : V, TensorProduct.map i i (δ v) = Coalgebra.comul (R := k) (i v)) (_hε : ∀ v : V, ε v = Coalgebra.counit (R := k) (i v)), (∀ v : V, TensorProduct.assoc k V V V (TensorProduct.map δ (LinearMap.id : V →ₗ[k] V) (δ v)) = TensorProduct.map (LinearMap.id : V →ₗ[k] V) δ (δ v)) ∧ (∀ v : V, TensorProduct.map ε (LinearMap.id : V →ₗ[k] V) (δ v) = TensorProduct.tmul k (1 : k) v) ∧ (∀ v : V, TensorProduct.map (LinearMap.id : V →ₗ[k] V) ε (δ v) = TensorProduct.tmul k v (1 : k))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
