<!-- theorem-id: fermat-p05/root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1.mismatched_support_zero-a1 -->

## Theorem `Submission.p05_ibsrm_mismatched_support_zero_a5b449214a`

Let R be a commutative ring, let n,p,t,d be natural numbers, let P be a matrix with rows Fin n and columns Fin p over R, and let rows:Fin d ↪ (Fin n ⊕ Fin t) and cols:Fin d ↪ (Fin p ⊕ Fin t) be embeddings. Put E=diag(P,I_t). Assume it is not the case that, for every a in Fin t, the predicates (∃i, rows(i)=inr(a)) and (∃j, cols(j)=inr(a)) are equivalent. Then det(E[rows,cols])=0.

Node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1.mismatched_support_zero-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/346

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_ibsrm_mismatched_support_zero_a5b449214a`

```lean
∀ {R : Type*} [CommRing R] (n p t d : ℕ) (P : Matrix (Fin n) (Fin p) R) (rows : Fin d ↪ (Fin n ⊕ Fin t)) (cols : Fin d ↪ (Fin p ⊕ Fin t)) (_h : ¬ (∀ a : Fin t, (∃ i : Fin d, rows i = Sum.inr a) ↔ (∃ j : Fin d, cols j = Sum.inr a))), Matrix.det ((Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix rows cols) = 0
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

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1.mismatched_support_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put M=E[rows,cols], and let S and T be the subsets of Fin t consisting of the identity indices selected by rows and cols, respectively. The hypothesis says that membership in S and T is not equivalent for every index. By classical logic there is an index a belonging to exactly one of S and T.
2. Suppose a belongs to S but not T. Choose i in Fin d with rows(i)=inr(a). For any j in Fin d, if cols(j)=inl(b), then M(i,j)=0 by the lower-left zero block. If cols(j)=inr(b), then b≠a, since otherwise a would belong to T. The identity-block entry at (a,b) is therefore zero. Thus every entry in row i of M is zero.
3. In the determinant formula det M=Σσ sign(σ)∏k M(k,σ(k)), every product contains M(i,σ(i))=0. Every summand is zero, so det M=0 in this case.
4. Suppose instead a belongs to T but not S. Choose j in Fin d with cols(j)=inr(a). For each i, an old row gives M(i,j)=0 by the upper-right zero block; a new row rows(i)=inr(b) has b≠a, because a is absent from S, and its identity-block entry is also zero. Thus column j is zero. For each determinant permutation σ, the factor indexed by k=σ⁻¹(j) is M(k,j)=0, so again every summand vanishes and det M=0.
5. These two cases exhaust the witness from step 1 and prove the conclusion. No nontriviality or positivity assumption was used; if d=0 or t=0, the mismatch hypothesis itself is impossible.

## Key steps

1. Extract an identity index selected on exactly one side.
2. A row-only identity index gives a zero row; a column-only identity index gives a zero column.
3. Every product in the determinant expansion contains an entry from that zero row or column.

## Reference use

### local-project

Queries:
- `det_fromBlocks|det_submatrix_equiv|det_permute|det_eq_zero_of_row_eq_zero|det_eq_zero_of_column_eq_zero|fromBlocks.*submatrix|submatrix.*fromBlocks`
- `p05_ibsrm_|reduce_minor|equivFin|orderIsoOfFin`
- `identity.*minor|minor.*identity|support.*fromBlocks|fromBlocks.*support|p05_ibsrm_`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Data/Matrix/Block.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Data/Finset/Sort.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p05-ibsrm-types-eqdyysp9/Types.lean`
- `/tmp/p05-ibsrm-types-eqdyysp9/Types.lean.log`
- `/tmp/p05-ibsrm-types-eqdyysp9/binding.json`

The snapshots match project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d; their tracked files and all nine installed dependency pins checked clean. The support/minor search found no matching theorem for the queried spellings. Inspected sources supply zero-row and zero-column determinant lemmas, permutation signs, simultaneous reindexing invariance, block determinant evaluation, and finite ordered enumeration. Both proposed types elaborate without warnings after import Submission from frozen proof base ece9f4a43483cf83ab2a417a07107d2da5436ffa. Entrywise checks confirm the matrix identity instance, and fromBlocks explicitly uses Matrix.of. Eight supporting declarations have transitive axiom closures containing only propext, Classical.choice and Quot.sound. Both proposed names remain unreserved. Disposable compilation verified policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, omitted only approved lines 10–11, and passed absence probes for all 13 targets. Exact omitted lines, reversible original/build hashes and check results are recorded in binding.json. The frozen proof base, contract, problem, header and handoff were preserved; a concurrent clean project advance was recorded separately. These checks establish interface compatibility, not comparator acceptance of either proposed theorem.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/605

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
