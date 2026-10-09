<!-- theorem-id: fermat-p05/root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1 -->

## Theorem `Submission.p05_ibs_reduce_minor_a5b449214a`

Let R be a commutative ring, let n,p,t,d be natural numbers, let P be an n-by-p matrix over R, and put E=diag(P,I_t), indexed by Fin n ⊕ Fin t and Fin p ⊕ Fin t. Given embeddings rows:Fin d ↪ (Fin n ⊕ Fin t) and cols:Fin d ↪ (Fin p ⊕ Fin t), either det(E[rows,cols])=0, or there exist a natural number l with l≤t and l≤d and embeddings rows':Fin(d−l) ↪ Fin n and cols':Fin(d−l) ↪ Fin p such that det(E[rows,cols]) equals det(P[rows',cols']) or its negative. Subtraction is truncated at zero and empty determinants are 1.

Node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/318

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/364, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/365

## Lean problem

Declaration: `Submission.p05_ibs_reduce_minor_a5b449214a`

```lean
∀ {R : Type*} [CommRing R] (n p t d : ℕ) (P : Matrix (Fin n) (Fin p) R) (rows : Fin d ↪ (Fin n ⊕ Fin t)) (cols : Fin d ↪ (Fin p ⊕ Fin t)), let E : Matrix (Fin n ⊕ Fin t) (Fin p ⊕ Fin t) R := Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R); Matrix.det (E.submatrix rows cols) = 0 ∨ ∃ l : ℕ, l ≤ t ∧ l ≤ d ∧ ∃ (rows' : Fin (d - l) ↪ Fin n) (cols' : Fin (d - l) ↪ Fin p), Matrix.det (E.submatrix rows cols) = Matrix.det (P.submatrix rows' cols') ∨ Matrix.det (E.submatrix rows cols) = -Matrix.det (P.submatrix rows' cols')
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

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let M=E[rows,cols]. Let S be the subset of Fin t consisting of indices a for which inr(a) occurs in the image of rows, and let T be the corresponding subset for cols. These are finite sets. Because rows and cols are embeddings, each selected index occurs exactly once.
2. If S≠T, one of S∖T and T∖S is nonempty. If a∈S∖T, choose the unique selected row with ambient index inr(a). At an old selected column its entry is zero because the lower-left block of E is zero. At a new selected column inr(b), one has b≠a because a∉T, so its entry is also zero. Thus M has a zero row, and every product in its determinant expansion contains a zero factor. Hence det M=0. If instead b∈T∖S, the corresponding selected column is zero by the same argument using the upper-right block and the identity block, and again det M=0. This proves the first alternative whenever S≠T.
3. Suppose S=T and set l=|S|. Since S⊆Fin t, l≤t. The positions of the selected new rows are in bijection with S, using rows and its injectivity, so there are l such positions and l≤d. The same holds for the selected new columns. Consequently exactly q=d−l selected rows and exactly q selected columns are old, and q+l=d.
4. Let A⊆Fin n and B⊆Fin p be the sets of old ambient row and column indices that occur. The preceding count gives |A|=|B|=q. Enumerate each set in increasing order to obtain embeddings rows':Fin q ↪ Fin n and cols':Fin q ↪ Fin p, and put C=P[rows',cols']. Enumerate S in increasing order as well. Reorder the d selected rows to list first the old indices in the order rows', then the new indices in that order of S; reorder the columns using cols' and the same order of S. These reorderings are permutations, since each listed ambient index occurs exactly once and every selected index has been listed.
5. In these orders, and identifying the first q and last l positions with Fin q ⊕ Fin l, the matrix is diag(C,I_l). The old-old entries are those of C, the mixed entries are zero, and the new-new entries are Kronecker deltas because the same distinct indices of S occur in the same order on both sides. Its determinant is det C: in the permutation expansion any term moving a new index has a zero factor from that identity row; the remaining terms fix all new indices and are precisely the signed terms defining det C. Simultaneous identification of the two index sets does not change the determinant.
6. Let ε be the product of the signs of the row and column permutations, regarded in R via the integer map. The permutation rule for determinants gives det C=ε det M. The integer sign product is either 1 or −1, and ε²=1 in every commutative ring. Multiplying the equality by ε therefore gives det M=ε det C. According to the sign, det M=det C or det M=−det C. Together with l≤t, l≤d and the embeddings from step 4, this is the second alternative.
7. All constructions use finite sets and their embeddings, so d=0, q=0, t=0, and the zero ring require no additional assumptions. If the initial embeddings do not exist, the universally quantified assertion has no such instance.

## Key steps

1. Compare the sets S and T of selected identity indices.
2. Use a mismatched identity index to exhibit a zero row or column.
3. When S=T, count l common identity indices and d−l old indices on each side.
4. Enumerate the old indices and reorder both selections with a common order on S.
5. Evaluate the resulting block determinant as the determinant of the old minor.
6. Undo the row and column signs to obtain equality with that minor or its negative.

## Reference use

### local-project

Queries:
- `rg -l --glob '*.lean' 'determinantal|minorIdeal|minor_ideal|fittingIdeal' .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae`
- `rg -n 'det_fromBlocks|det_submatrix_equiv|det_permute|det_eq_zero_of_row|det_eq_zero_of_column|det_succ' .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant`
- `sed -n '200,238p;350,366p;665,685p;720,730p' .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `sed -n '45,115p' .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Data/Matrix/Block.lean`
- `git show 2e63b83283924ad7800c72a157d379c90498ccf3:Submission.lean`
- `rg -n 'p05_ibs_extend_minor_a5b449214a|p05_ibs_reduce_minor_a5b449214a' Submission.lean .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Data/Matrix/Block.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p05-ibs-decomposition-3dl5o7zb/ChildTypes.lean`
- `/tmp/p05-ibs-decomposition-3dl5o7zb/ChildTypes.lean.log`
- `/tmp/p05-ibs-decomposition-3dl5o7zb/binding.json`

The project and mathlib snapshots match manifest revisions 2fdd42759f4ab17640ac773289b521dd69d4b26e and db584cd6d46c92f209a44c0f1c829460d327499d; tracked files and all nine installed dependency pins checked clean. The determinantal-ideal search returned no matches for the queried spellings. Inspected sources provide block determinant evaluation, simultaneous reindexing invariance, permutation signs, and zero-row/column determinants; fromBlocks constructs a Matrix via Matrix.of. The active DAG identifies this as the depth-4 identity-block helper and already supplies successive-minor containment. Both proposed names remain unreserved. Both exact child types elaborate after import Submission with Lean 4.33.1, and an anonymous entrywise check verifies the identity-matrix instance. Seven supporting determinant declarations have transitive axiom closures containing only propext, Classical.choice, and Quot.sound. Disposable compilation used the matching policy entry and verified digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, omitted only lines 10–11, and passed Lean absence probes for all 13 targets. Reversible original/build hashes and successful diagnostics are recorded in binding.json. Protected artifacts remain unchanged. These are decomposition diagnostics, not comparator acceptance of a theorem.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/619

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
