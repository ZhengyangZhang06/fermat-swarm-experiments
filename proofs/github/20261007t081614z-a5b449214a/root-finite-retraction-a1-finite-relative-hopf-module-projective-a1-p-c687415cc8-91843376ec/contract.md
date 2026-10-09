<!-- theorem-id: fermat-p05/root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1.matching_support_blocks-a1 -->

## Theorem `Submission.p05_ibsrm_matching_support_blocks_a5b449214a`

Let R be a commutative ring, let n,p,t,d be natural numbers, let P be a matrix with rows Fin n and columns Fin p over R, and let rows:Fin d ↪ (Fin n ⊕ Fin t) and cols:Fin d ↪ (Fin p ⊕ Fin t) be embeddings. Assume that for every a in Fin t, some rows(i) equals inr(a) if and only if some cols(j) equals inr(a). Put E=diag(P,I_t) and M=E[rows,cols]. There exist a natural number l≤t with l≤d, embeddings rows':Fin(d−l) ↪ Fin n and cols':Fin(d−l) ↪ Fin p, and equivalences er,ec:(Fin(d−l) ⊕ Fin l) ≃ Fin d such that M[er,ec]=diag(P[rows',cols'],I_l). Subtraction is truncated; zero dimensions and the zero ring are allowed.

Node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1.matching_support_blocks-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/346

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_ibsrm_matching_support_blocks_a5b449214a`

```lean
∀ {R : Type*} [CommRing R] (n p t d : ℕ) (P : Matrix (Fin n) (Fin p) R) (rows : Fin d ↪ (Fin n ⊕ Fin t)) (cols : Fin d ↪ (Fin p ⊕ Fin t)) (_h : ∀ a : Fin t, (∃ i : Fin d, rows i = Sum.inr a) ↔ (∃ j : Fin d, cols j = Sum.inr a)), ∃ l : ℕ, l ≤ t ∧ l ≤ d ∧ ∃ (rows' : Fin (d - l) ↪ Fin n) (cols' : Fin (d - l) ↪ Fin p) (er ec : (Fin (d - l) ⊕ Fin l) ≃ Fin d), ((Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix rows cols).submatrix er ec = Matrix.fromBlocks (P.submatrix rows' cols') 0 0 (1 : Matrix (Fin l) (Fin l) R)
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
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1.matching_support_blocks-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define finite subsets A={a in Fin n | ∃i, rows(i)=inl(a)}, B={b in Fin p | ∃j, cols(j)=inl(b)}, and S={a in Fin t | ∃i, rows(i)=inr(a)}. The support hypothesis also identifies S with {a in Fin t | ∃j, cols(j)=inr(a)}.
2. Sending a row position i to its selected ambient index, in A for an old index or in S for a new index, gives a bijection br:Fin d→A⊕S. Indeed, every position has exactly one of these forms; equal outputs imply equal ambient row indices and hence equal positions by injectivity of rows; every element of A or S has a preimage by its defining membership. Likewise the column selection gives a bijection bc:Fin d→B⊕S: injectivity follows from cols, old-column surjectivity follows from the definition of B, and new-column surjectivity follows from the support hypothesis.
3. Set l=|S|. Since S is a subset of Fin t, l≤t. Counting the two bijections gives d=|A|+l and d=|B|+l. Hence l≤d. Set q=d−l; these equalities give |A|=q, |B|=q and q+l=d, including when one of these numbers is zero.
4. List A and B in increasing order to obtain bijections α:Fin q→A and β:Fin q→B; list S in increasing order to obtain a bijection γ:Fin l→S. Such lists exist for every finite subset of a finite linear order and contain each element exactly once. Composing α and β with the inclusions into Fin n and Fin p gives embeddings rows' and cols'. Write s:Fin l→Fin t for γ followed by inclusion; s is injective.
5. Define er=br⁻¹∘(α⊕γ) and ec=bc⁻¹∘(β⊕γ). These are equivalences from Fin q⊕Fin l to Fin d because both factors in each composite are bijections. Their defining identities are rows(er(inl i))=inl(rows'(i)), rows(er(inr a))=inr(s(a)), cols(ec(inl j))=inl(cols'(j)), and cols(ec(inr b))=inr(s(b)).
6. Let N=M[er,ec] and C=P[rows',cols']. The identities in step 5 show that N(inl i,inl j)=C(i,j), N(inl i,inr b)=0, and N(inr a,inl j)=0 by the three corresponding blocks of E. The remaining entry is N(inr a,inr b)=I_t(s(a),s(b)). Since s is injective, s(a)=s(b) if and only if a=b, so this entry equals I_l(a,b). This equality of Kronecker-delta expressions is valid in every commutative ring, including the zero ring.
7. Every row and column index of N belongs to one of the two summands, so the four entry computations prove N=diag(C,I_l) by matrix extensionality. The number l, bounds from step 3, embeddings from step 4 and equivalences from step 5 are the required witnesses. Empty enumerations and empty blocks satisfy the same constructions, so no separate nonempty hypothesis is needed.

## Key steps

1. Identify the common selected identity support S and the old row and column supports A and B.
2. Build bijections Fin d≃A⊕S and Fin d≃B⊕S using the embedding hypotheses.
3. Count l=|S| and q=d−l, proving the bounds and |A|=|B|=q.
4. Enumerate A, B and S, using the same enumeration of S on both sides.
5. Compose these enumerations with the inverse selection bijections to construct er and ec.
6. Check the four blocks entrywise and use injectivity of the common enumeration to identify the identity block.

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

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
