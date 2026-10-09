<!-- theorem-id: fermat-p05/root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.section_of_inner_inverse-a1 -->

## Theorem `Submission.p05_ums_section_of_inner_inverse_a5b449214a`

Let R be a commutative ring and let F,G,M be R-modules with underlying additive commutative groups. Let f:G→F, g:F→G, and π:F→M be R-linear maps. Assume (f∘g)∘f=f, π is surjective, and ker π=im f. Then there exists an R-linear map s:M→F with π∘s=id_M. No freeness, finiteness, or nontriviality assumptions are required.

Node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.section_of_inner_inverse-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/279

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_ums_section_of_inner_inverse_a5b449214a`

```lean
∀ {R : Type*} [CommRing R] {F : Type*} [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G] {M : Type*} [AddCommGroup M] [Module R M] (f : G →ₗ[R] F) (g : F →ₗ[R] G) (π : F →ₗ[R] M) (_hinner : (f.comp g).comp f = f) (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range f), ∃ s : M →ₗ[R] F, π.comp s = LinearMap.id
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

- Parent DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1`
- Child DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.section_of_inner_inverse-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define the linear endomorphism e=f∘g of F. The identity (f∘g)∘f=f says e(f(y))=f(y) for every y in G. Therefore r=id_F-e annihilates the image of f: r(f(y))=0. Moreover, e(x) lies in the image of f and hence in ker π for every x, so π(r(x))=π(x).
2. If π(x)=π(x'), then x-x' belongs to ker π=im f. Choose y with f(y)=x-x'. The previous step gives r(x)-r(x')=r(x-x')=r(f(y))=0. Consequently r(x)=r(x').
3. Surjectivity of π provides a preimage x of each m in M. Define s(m)=r(x). Step 2 proves that this value is independent of the chosen preimage, so it defines a function M→F. Equivalently, choose one preimage for each m and use Step 2 to replace that choice by any other preimage when computing s.
4. The element 0 of F is a preimage of 0 in M, so s(0)=r(0)=0. If x and y are preimages of m and m', then x+y is a preimage of m+m'; hence s(m+m')=r(x+y)=r(x)+r(y)=s(m)+s(m'). For a in R, ax is a preimage of am, and therefore s(am)=r(ax)=a r(x)=a s(m). Thus s is R-linear.
5. For any m, choose x with π(x)=m. Step 1 gives π(s(m))=π(r(x))=π(x)=m. Equality at every m proves π.comp s=LinearMap.id. This uses no freeness, finiteness, positivity, or nontriviality assumptions.

## Key steps

1. Define r=id_F−fg; show that r annihilates im f and satisfies πr=π.
2. Use ker π=im f to show r takes equal values on equal π-fibers.
3. Define s on M using preimages under the surjective map π.
4. Prove additivity and scalar compatibility using independence of the chosen preimages.
5. Verify πs=id_M pointwise.

## Reference use

### local-project

Queries:
- `inner.inverse|generalized.inverse|unit_minor|unit.*minor|split.*minor`
- `det_fromBlocks|isUnit_iff_isUnit_det|mul_adjugate|adjugate_mul|det_updateRow|det_succ`
- `mulVecLin_mul|mulVecLin.*comp|def mulVecLin|def liftOfSurjective|liftOfSurjective`
- `range.*[Cc]ompl|exists.*[Rr]ight[Ii]nverse|ofBijective|liftQ|isIdempotentElem_iff`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean HeaderPolicyCheck.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean CheckAll.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Projection.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-5b68ec51cc/decomposition-ums-diagnostics-y5c5gqal/build/CheckAll.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-5b68ec51cc/decomposition-ums-diagnostics-y5c5gqal/interface-report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-5b68ec51cc/decomposition-ums-diagnostics-y5c5gqal/name-audit.json`

The targeted project search found no matching inner-inverse or unit-minor splitting theorem. Pinned mathlib supplies adjugate identities, Schur-complement determinants, Matrix.mulVecLin_mul, and quotient/projection infrastructure. Both snapshots and all nine compiler dependencies matched their clean pins. Both literal child types elaborate after import Submission; anonymous checks verify genuine matrix multiplication by its finite-sum formula, scalar IsUnit semantics, and conditional assembly of the exact frozen parent. Six inspected infrastructure declarations have transitive axiom closures contained in propext, Classical.choice, and Quot.sound. Proposed names are absent from the imported environment, current Submission, and ten DAG registries. Private compiler copies omit exactly lines 10–11 under policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; Lean confirms all 13 targets absent. The receipt records exact omissions and reversible original/build hashes. The frozen contract, problem record, and handoff remain unchanged. These are interface diagnostics; proof acceptance still requires the configured comparator and independent review.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/415

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
