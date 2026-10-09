<!-- theorem-id: fermat-p05/root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.base_changed_presentation-a1 -->

## Theorem `Submission.p05_fr_rhm_bcsi_base_changed_presentation_a5b449214a`

Let R and S be commutative rings with an R-algebra structure on S, and write φ:R→S for the structure map. Let M be an R-module with commutative additive group. Let n,p be natural numbers, let P be an n-by-p matrix over R, and let π:R^n→M be a surjective R-linear map with ker(π)=im(P), where P acts by matrix-vector multiplication. Let P_S have entries φ(P_ij). Give S⊗_R M the S-action on its first factor. Then there exists an S-linear map q:S^n→S⊗_R M such that q(b)=Σ_i b_i·(1⊗π(e_i)) for every b, q is surjective, and ker(q)=im(P_S). Here e_i is the ith standard coordinate vector; zero n and zero p are allowed.

Node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.base_changed_presentation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/282

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_fr_rhm_bcsi_base_changed_presentation_a5b449214a`

```lean
∀ {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {M : Type*} [AddCommGroup M] [Module R M] (n p : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M) (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin), ∃ q : (Fin n → S) →ₗ[S] TensorProduct R S M, (∀ b : Fin n → S, q b = ∑ i, b i • TensorProduct.tmul R (1 : S) (π (Pi.single i (1 : R)))) ∧ Function.Surjective q ∧ LinearMap.ker q = LinearMap.range (P.map (algebraMap R S)).mulVecLin
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
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.base_changed_presentation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write φ for the algebra map, let e_i denote standard coordinate vectors, put m_i=π(e_i), and let P_S be P with φ applied entrywise. Define q(b)=Σ_i b_i·(1⊗m_i). Distributivity and associativity of the first-factor S-action show q(b+b')=q(b)+q(b') and q(sb)=s q(b). Thus q is an S-linear map with the asserted formula.
2. For m∈M choose a∈R^n with π(a)=m. The coordinate identity a=Σ_i a_i e_i implies m=Σ_i a_i m_i. Tensor additivity and balancing give s⊗m=Σ_i sφ(a_i)·(1⊗m_i). This equals q applied to the tuple with coordinates sφ(a_i). Every tensor is a finite sum of pure tensors, and the image of q is closed under sums. Therefore q is surjective.
3. Let N=im(P_S). For each column j, let f_j be the corresponding standard vector in the domain of the matrix. The hypothesis im(P)=ker(π) gives π(Pf_j)=0. Consequently q(P_S f_j)=Σ_i φ(P_ij)·(1⊗m_i)=1⊗π(Pf_j)=0, using the standard vector over the appropriate coefficient ring in each occurrence. Every P_S c is the sum of c_j times these columns, so N⊆ker(q). Hence q induces an S-linear map α:C→S⊗_R M on C=S^n/N, with α([b])=q(b).
4. Regard C as an R-module via φ and define v:R^n→C by v(a)=[(φ(a_i))_i]. This map is R-linear. If a=Pd, preservation of sums and products by φ gives (φ(a_i))_i=P_S(φ(d_j))_j, so v(a)=0. Thus v kills ker(π). Define β(m)=v(a) for any lift π(a)=m. Two lifts differ by an element of ker(π), so this definition is independent of the lift. Using lifts a+a' and ra proves additivity and R-linearity of β. In particular β(m_i)=[e_i], now with e_i the standard vector over S.
5. The map (s,m)↦s·β(m) is additive in both arguments and R-balanced: s·β(rm)=sφ(r)·β(m). The tensor universal property therefore gives β̂:S⊗_R M→C with β̂(s⊗m)=s·β(m). Multiplication of the first tensor factor by t multiplies this image by t. Since pure tensors generate, β̂ is S-linear.
6. For every i, β̂α([e_i])=β̂(1⊗m_i)=β(m_i)=[e_i]. The classes [e_i] generate C over S, so β̂α is the identity. Conversely αβ̂(s⊗m_i)=α(s[e_i])=s·(1⊗m_i)=s⊗m_i. Step 2 expresses every pure tensor as an S-linear combination of the 1⊗m_i, so αβ̂ is also the identity. In particular α is injective.
7. Since q(b)=α([b]) and α is injective, q(b)=0 if and only if [b]=0, which is equivalent to b∈N. Therefore ker(q)=im(P_S). Together with steps 1 and 2, this proves every clause of the conclusion. All coordinate identities and sums used above remain valid when n or p is zero.

## Key steps

1. Define the canonical S-linear map from the images of the standard generators.
2. Use surjectivity of π and tensor balancing to prove surjectivity of q.
3. Show the mapped relation columns vanish and descend q to their cokernel.
4. Factor the coordinatewise algebra-map quotient through π to construct β.
5. Extend β by the balanced tensor universal property.
6. Check the two induced maps are inverse on generating elements.
7. Deduce the exact kernel equality from injectivity of the cokernel-to-tensor map.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/409

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
