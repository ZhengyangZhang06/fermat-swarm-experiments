<!-- theorem-id: fermat-p05/root.finite_retraction-a1.coideal_ideal_dichotomy-a1 -->

## Theorem `Submission.p05_fr_coideal_ideal_dichotomy_a5b449214a`

Let k be a field and A a commutative Hopf k-algebra. Let J be an ideal of A. Suppose that, for every x∈J, Δ(x) belongs to the k-linear span of tensors a⊗b with a∈J and b∈A. Then J is the zero ideal or the whole ring.

Node: `root.finite_retraction-a1.coideal_ideal_dichotomy-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/232

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_fr_coideal_ideal_dichotomy_a5b449214a`

```lean
∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A] (J : Ideal A) (_hJ : ∀ x ∈ J, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k A A | ∃ a ∈ J, ∃ b : A, t = TensorProduct.tmul k a b}), J = ⊥ ∨ J = ⊤
```

### Frozen project context

`Fermat/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean` at `2fdd42759f4ab17640ac773289b521dd69d4b26e` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.hopfKer_eq_of_surjective_of_ker_eq_span
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    {B : Type w} [CommRing B] [Bialgebra k B] (q : H →ₐc[k] B) (hq : Function.Surjective q)
    (hker : RingHom.ker (q : H →+* B) =
      Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}) :
    HopfAlgebra.hopfKer q = K := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1`
- Child DAG node: `root.finite_retraction-a1.coideal_ideal_dichotomy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. If J is the whole ring, the second conclusion holds. Assume henceforth that J is proper. An ideal of A is closed under k-scalar multiplication, since a scalar acts by multiplication by its image in A.
2. The k-linear map L:A⊗_k A→A defined by L(a⊗b)=aS(b) sends every tensor with a∈J into J. Consequently it sends their k-linear span into J. For x∈J the hypothesis and the antipode identity therefore give ε(x)1=L(Δ(x))∈J.
3. If ε(x) were nonzero, ε(x)1 would have inverse ε(x)⁻¹1. A proper ideal cannot contain a unit. Hence ε(x)=0 for every x∈J.
4. The k-linear map C:A⊗_k A→A defined by C(a⊗b)=ε(a)b vanishes on every generating tensor whose first factor belongs to J, by step 3. It therefore vanishes on Δ(x) for x∈J. The counit identity also gives C(Δ(x))=x. Thus every x∈J is zero, proving J is the zero ideal.

## Key steps

1. Reduce to the case of a proper ideal.
2. Apply multiplication after id⊗S to show ε(x)1 belongs to J.
3. Use the field hypothesis and properness to show ε vanishes on J.
4. Apply ε⊗id and the counit identity to conclude J=0.

## Reference use

### local-project

Queries:
- `class.*[Cc]omodule|structure.*[Cc]omodule|fittingIdeal|fitting_ideal|Fitting ideal`
- `Fitting|fittingIdeal|fitting_ideal|class.*[Cc]omodule|structure.*[Cc]omodule|antipode_mul|antipodeAlgHom`
- `isNoetherianRing_of_fg|finitePresentation_of_finite|exists.*[Ss]ection|exists.*[Ll]eftInverse|projective.*iff`
- `def mulVecLin|mulVecLin_apply|def lsmul|def mulLeft|submatrix`
- `p05_fr_coideal_ideal_dichotomy_a5b449214a|p05_fr_projective_of_trivial_minors_a5b449214a|p05_fr_finite_relative_hopf_module_projective_a5b449214a`
- `rg --files -uu /mnt/data/zhengyang-workspace/fermat-swarm-projects -g dag.json`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean CheckTypes.lean > ../literal-types.log 2>&1`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean CheckInstances.lean > ../instances-axioms.log 2>&1`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean HeaderPolicyCheck.lean > ../header-absence.log 2>&1`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Adjoin/FG.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/Projective.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Algebra/Tower.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p05-fr-decomp-mgjv880w/challenge/CheckTypes.lean`
- `/tmp/p05-fr-decomp-mgjv880w/challenge/CheckInstances.lean`
- `/tmp/p05-fr-decomp-mgjv880w/header-input-binding.json`
- `/tmp/p05-fr-decomp-mgjv880w/header-absence.log`
- `/tmp/p05-fr-decomp-mgjv880w/instances-axioms.log`
- `/tmp/p05-fr-decomp-mgjv880w/report.json`

The project and mathlib snapshots are clean at 2fdd42759f4ab17640ac773289b521dd69d4b26e and db584cd6d46c92f209a44c0f1c829460d327499d; all nine dependency checkouts match their clean pins. The snapshot supplies antipode multiplicativity, finite-presentation infrastructure, matrix presentation maps, and projective lifting. No Fitting-ideal or general comodule declaration matched the targeted search. The three proposed names have no active-DAG collision. All three literal types elaborate warning-clean after import Submission. Anonymous proofs verify the tensor action and matrix-vector semantics; nine inspected infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. Disposable compiler copies follow policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, omitting exactly lines 10–11; Lean confirms all 13 targets absent. Reversible original/build hashes are retained in header-input-binding.json. Protected sources and handoffs were not edited. These are interface diagnostics; theorem acceptance still requires the configured exact-contract comparator and independent review.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/298

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
