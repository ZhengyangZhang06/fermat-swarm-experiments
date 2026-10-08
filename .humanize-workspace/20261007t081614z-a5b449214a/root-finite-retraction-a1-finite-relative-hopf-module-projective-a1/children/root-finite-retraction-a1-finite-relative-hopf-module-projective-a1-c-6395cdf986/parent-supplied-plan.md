# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-c-6395cdf986/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1`
- Child key: `coaction_twist`
- Declaration: `Submission.p05_fr_rhm_coaction_twist_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A] {H : Type*} [CommRing H] [HopfAlgebra k H] (ι : BialgHom k A H) {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [Module (TensorProduct k A H) (TensorProduct k M H)] (_hact : ∀ (a : A) (h : H) (m : M) (g : H), (TensorProduct.tmul k a h) • (TensorProduct.tmul k m g) = TensorProduct.tmul k (a • m) (h * g)) (μ : M →ₗ[k] TensorProduct k M H) (_hcoassoc : ∀ m : M, TensorProduct.assoc k M H H ((TensorProduct.map μ (LinearMap.id : H →ₗ[k] H)) (μ m)) = (TensorProduct.map (LinearMap.id : M →ₗ[k] M) (Coalgebra.comul (R := k))) (μ m)) (_hcounit : ∀ m : M, TensorProduct.rid k M ((TensorProduct.map (LinearMap.id : M →ₗ[k] M) (Coalgebra.counit (R := k))) (μ m)) = m) (_hcompat : ∀ (a : A) (m : M), let d := Coalgebra.Repr.arbitrary k a; μ (a • m) = ∑ i ∈ d.index, TensorProduct.map ((Algebra.lsmul k k M) (d.left i)) (LinearMap.mulLeft k (ι (d.right i))) (μ m)), ∃ (θ : TensorProduct k A H ≃ₐ[k] TensorProduct k A H) (T : TensorProduct k M H ≃ₗ[k] TensorProduct k M H), (∀ (a : A) (h : H), θ (TensorProduct.tmul k a h) = (TensorProduct.map (LinearMap.id : A →ₗ[k] A) ι.toLinearMap) (Coalgebra.comul (R := k) a) * TensorProduct.tmul k (1 : A) h) ∧ (∀ (m : M) (h : H), T (TensorProduct.tmul k m h) = TensorProduct.map (LinearMap.id : M →ₗ[k] M) (LinearMap.mulLeft k h) (μ m)) ∧ (∀ (s : TensorProduct k A H) (x : TensorProduct k M H), T (s • x) = θ s • T x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
