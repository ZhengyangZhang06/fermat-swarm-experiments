<!-- theorem-id: fermat-p05/root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.twisted_presentation-a1 -->

## Theorem `Submission.p05_fr_rhm_bcsi_twisted_presentation_a5b449214a`

Let S be a commutative ring and L an S-module with commutative additive group. Let n,p be natural numbers, P an n-by-p matrix over S, and q:S^n→L a surjective S-linear map with ker(q)=im(P), where P acts by matrix-vector multiplication. Let θ:S→S be a ring automorphism and T:L→L an additive equivalence satisfying T(sx)=θ(s)T(x) for every s∈S and x∈L. Let Pθ have entries θ(P_ij). Then there exists an S-linear map qθ:S^n→L such that qθ(b)=T(q((θ⁻¹(b_i))_i)) for every b, qθ is surjective, and ker(qθ)=im(Pθ). Zero n and zero p are allowed.

Node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.twisted_presentation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/282

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_fr_rhm_bcsi_twisted_presentation_a5b449214a`

```lean
∀ {S : Type*} [CommRing S] {L : Type*} [AddCommGroup L] [Module S L] (n p : ℕ) (P : Matrix (Fin n) (Fin p) S) (q : (Fin n → S) →ₗ[S] L) (_hq : Function.Surjective q) (_hker : LinearMap.ker q = LinearMap.range P.mulVecLin) (θ : S ≃+* S) (T : L ≃+ L) (_hT : ∀ (s : S) (x : L), T (s • x) = θ s • T x), ∃ qθ : (Fin n → S) →ₗ[S] L, (∀ b : Fin n → S, qθ b = T (q (fun i => θ.symm (b i)))) ∧ Function.Surjective qθ ∧ LinearMap.ker qθ = LinearMap.range (P.map θ.toRingHom).mulVecLin
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

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.twisted_presentation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define A(b)_i=θ⁻¹(b_i) for b∈S^n and define qθ(b)=T(q(A(b))). The maps A, q and T are additive, so qθ is additive. For s∈S, A(sb)=θ⁻¹(s)A(b). S-linearity of q and the assumed semilinearity of T give qθ(sb)=T(θ⁻¹(s)q(A(b)))=θ(θ⁻¹(s))T(q(A(b)))=s qθ(b). Hence the displayed formula defines an S-linear map qθ and proves its asserted value on every tuple.
2. For y∈L, surjectivity of q supplies a∈S^n with q(a)=T⁻¹(y). Set b_i=θ(a_i). Then A(b)=a and qθ(b)=T(T⁻¹(y))=y. Therefore qθ is surjective.
3. Put Pθ=P.map θ.toRingHom, and interpret application of θ or θ⁻¹ to a tuple coordinatewise. Since θ preserves finite sums and products, every c∈S^p satisfies θ((Pc)_i)=Σ_j θ(P_ij)θ(c_j)=(Pθ(θ(c)))_i. Applying θ⁻¹ likewise gives A(Pθ d)=P(θ⁻¹(d)) for every d∈S^p. These identities also hold for empty index sets.
4. Additivity gives T(0)=0, and T is injective. Therefore qθ(b)=0 if and only if q(A(b))=0. The equality ker(q)=im(P) makes this equivalent to A(b)=Pc for some c∈S^p. Applying θ coordinatewise and using step 3 gives b=Pθ(θ(c)), so b∈im(Pθ).
5. Conversely, if b=Pθ d, the inverse identity in step 3 gives A(b)=P(θ⁻¹(d)). This belongs to im(P)=ker(q), so qθ(b)=T(0)=0. Both containments establish ker(qθ)=im(Pθ). Together with the formula and surjectivity proved in steps 1 and 2, this establishes the full conclusion.

## Key steps

1. Conjugate coefficient vectors by θ⁻¹ and compose with q and T.
2. Use semilinearity to prove the resulting map is S-linear.
3. Construct a preimage of any element using q's surjectivity and the inverse of T.
4. Establish coordinatewise compatibility of θ with matrix-vector multiplication.
5. Use injectivity of T and the original kernel equality to prove both inclusions for the twisted kernel.

## Reference use

### local-project

Queries:
- `determinantal|fittingideal|fitting ideal`
- `rTensor_exact|lTensor_exact|map_det|map_span|baseChange.*surjective|baseChange.*exact`
- `def mulVecLin|mulVecLin_apply|def hopfKer|theorem hopfKer`
- `smul_tmul|tmul_smul`
- `rg --files -uu /mnt/data/zhengyang-workspace/fermat-swarm-projects -g dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Ideal/Maps.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p05-bcsi-decomp-va00aen4/CheckTypes.lean`
- `/tmp/p05-bcsi-decomp-va00aen4/CheckTypes.lean.log`
- `/tmp/p05-bcsi-decomp-va00aen4/Absence.lean.log`
- `/tmp/p05-bcsi-decomp-va00aen4/header-input-binding.json`
- `/tmp/p05-bcsi-decomp-va00aen4/report.json`

The clean snapshots match project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d; all nine compiler dependency checkouts match their clean pins. The targeted determinantal/Fitting-ideal search found no matching API in mathlib's LinearAlgebra and RingTheory directories. Relevant infrastructure includes lTensor_exact, LinearMap.baseChange_surjective, Matrix.mulVecLin_apply, RingHom.map_det, and Ideal.map_span. Both literal child types elaborate after import Submission at the fixed proof-base ca1bb49d173a82f6c760dd27fdde39c92765501e. Anonymous proofs verify the first-factor S-action and both mapped matrix-vector formulas. Six inspected infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. Neither proposed name collides with the ten scanned active DAGs or current Submission. Disposable compiler copies omit exactly policy-listed lines 10–11 under policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; Lean confirms all 13 targets absent, and reversible original/build hashes are recorded. The frozen contract and Submission header remain intact. These are interface diagnostics, not comparator acceptance of a theorem.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/378

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
