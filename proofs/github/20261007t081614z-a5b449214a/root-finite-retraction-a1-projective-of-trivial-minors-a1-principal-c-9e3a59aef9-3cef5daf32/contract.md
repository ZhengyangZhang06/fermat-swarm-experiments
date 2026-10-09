<!-- theorem-id: fermat-p05/root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1.patch_power_sections-a1 -->

## Theorem `Submission.p05_pcs_patch_power_sections_a5b449214a`

Let R be a commutative ring, F and M be R-modules, and π:F→M an R-linear map. Let q be a natural number and f:Fin q→R satisfy Ideal.span(range f)=R. Suppose N:Fin q→ℕ has N_i>0 for every i, and t_i:M→F are R-linear maps satisfying π∘t_i=f_i^{N_i}id_M for every i. Then there exists an R-linear section s:M→F of π.

Node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1.patch_power_sections-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/280

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_pcs_patch_power_sections_a5b449214a`

```lean
∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {F : Type*} [AddCommGroup F] [Module R F] (π : F →ₗ[R] M) (q : ℕ) (f : Fin q → R) (_hcover : Ideal.span (Set.range f) = ⊤) (N : Fin q → ℕ) (_hN : ∀ i, 0 < N i) (t : Fin q → M →ₗ[R] F) (_ht : ∀ i, π.comp (t i) = (f i) ^ (N i) • (LinearMap.id : M →ₗ[R] M)), ∃ s : M →ₗ[R] F, π.comp s = LinearMap.id
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

- Parent DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1`
- Child DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1.patch_power_sections-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. If 1=0 in R, every element of M and F equals zero by x=1·x=0·x. The zero map s:M→F is then a section of π. Assume henceforth 1≠0. The cover condition implies q>0, because an empty range generates the zero ideal, which cannot contain 1.
2. Let J be the set of sums Σ_i a_i f_i with a:Fin q→R. It is an ideal: zero coefficients give zero, coefficientwise addition and negation give additive closure, and multiplying all coefficients by r gives closure under multiplication by r. Each f_i belongs to J by taking coefficient 1 at i and 0 elsewhere. Therefore Ideal.span(range f)⊆J. The cover hypothesis gives coefficients a_i with 1=Σ_i a_i f_i.
3. Put L=1+Σ_i(N_i−1). Then L>0. Repeated finite distributivity expands 1=(Σ_i a_i f_i)^L as Σ_α ∏_{r∈Fin L}(a_{α(r)}f_{α(r)}), where α ranges over all functions Fin L→Fin q. For each α let k_i be the number of positions r with α(r)=i. These fibers partition Fin L, so Σ_i k_i=L. If every k_i<N_i, positivity of N_i gives k_i≤N_i−1 and hence L≤Σ_i(N_i−1)=L−1, a contradiction. Choose, for example, the least index i(α) with N_{i(α)}≤k_{i(α)}.
4. Reordering products by commutativity, the α summand equals (∏_r a_{α(r)})∏_j f_j^{k_j}. With i=i(α), define r_α=(∏_r a_{α(r)}) f_i^{k_i−N_i} ∏_{j≠i} f_j^{k_j}. Since k_i≥N_i, the exponent law gives that summand equal to r_α f_i^{N_i}. This uses multiplication and powers only, so no cancellation or domain assumption is needed. Define b_i as the sum of r_α over the finitely many α with i(α)=i. Grouping the expansion in Step 3 yields 1=Σ_i b_i f_i^{N_i}.
5. Define s=Σ_i b_i t_i in the R-module of R-linear maps M→F. For every m∈M, linearity of π and the assumed equalities π∘t_i=f_i^{N_i}id_M give π(s(m))=Σ_i b_i π(t_i(m))=Σ_i(b_i f_i^{N_i})m=(Σ_i b_i f_i^{N_i})m=m. Thus π.comp s=LinearMap.id. Neither finite generation nor surjectivity of π is required beyond the stated hypotheses.

## Key steps

1. Handle the zero ring and exclude an empty cover in a nonzero ring.
2. Express 1 as an indexed linear combination of the cover elements.
3. Expand a sufficiently high power and count occurrences to find a prescribed power dividing every summand.
4. Group summands to express 1 as a linear combination of the powers f_i^{N_i}.
5. Use those coefficients to combine the power-scaled sections into a section.

## Reference use

### local-project

Queries:
- `span_range_pow_eq_top|span_range_eq_top`
- `def map|map_mk|mk_eq_zero|mk_eq_mk|mk_surjective|exists.*eq|def lift|exists.*lift|eq_zero`
- `pcs_clear_away_section|pcs_patch_power_sections`
- `sed -n '1,210p' .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/LocalProperties/Projective.lean`
- `sed -n '259,340p' .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Localization/Module.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean HeaderAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean CheckTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/LocalizedModule/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Localization/Module.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Ideal/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/LocalProperties/Projective.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-principal-c-fd30309f6a/parent-child-handoff.json`
- `/tmp/p05-pcs-decomposition-at0a8zqn/latest-build/CheckTypes.lean`
- `/tmp/p05-pcs-decomposition-at0a8zqn/latest-CheckTypes.log`
- `/tmp/p05-pcs-decomposition-at0a8zqn/latest-HeaderAbsence.log`
- `/tmp/p05-pcs-decomposition-at0a8zqn/latest-interface-report.json`
- `/tmp/p05-pcs-decomposition-at0a8zqn/name-audit.json`
- `/tmp/p05-pcs-decomposition-at0a8zqn/pins.json`

The handoff identifies the supplied statement as the depth-3 principal_cover_splitting child of the frozen Hopf-kernel problem. The clean reference revisions are project 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine compiler dependencies also match clean pins. Relevant infrastructure includes LocalizedModule.mk_eq, induction_on, IsLocalizedModule.eq_zero_iff, the localization-linear map and its fraction formula, Ideal.span_range_pow_eq_top, and a maximal-localization splitting criterion. Both proposed literal types elaborate after import Submission; five anonymous checks verify matrix-vector multiplication, localization-ring linearity, the fraction formula, and scalar actions on linear maps. The six inspected library declarations have transitive axioms contained in propext, Classical.choice, and Quot.sound. Neither proposed name occurs in the ten DAG registries or imported environment. Final diagnostics bind to committed Submission snapshot ece863bfb9eb10d11de9b493e72d7f6223b12084. Disposable compiler copies omit exactly policy-listed lines 10–11 under policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; Lean confirms all 13 targets absent. Exact omitted text and reversible hashes are recorded in latest-interface-report.json. These are interface checks, not proof acceptance; the configured comparator and independent review remain required.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/473

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
