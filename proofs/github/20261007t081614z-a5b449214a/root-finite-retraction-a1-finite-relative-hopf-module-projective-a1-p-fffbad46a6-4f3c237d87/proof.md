# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put E=diag(P,I_t), s=n−r and d=n+t−r, with truncated subtraction. Write D_a for the ideal of a-minors of the indicated matrix. Empty selections show D_0(C)=R for every C. The successive-minor containment, applied repeatedly, gives D_b(P)⊆D_a(P) whenever a≤b.
2. First suppose n≤r. Then s=0 and d≤t. Select d matching rows and columns entirely in the identity block, using the first d indices of Fin t in both selections. The resulting matrix is I_d and its determinant is 1, including d=0. Consequently D_d(E)=R=D_s(P).
3. Now suppose r<n. Then s=n−r>0 and d=s+t. For each s-minor of P, append all t new rows and all t new columns, ordering the old selections first and the new indices last. These are injective selections of size d. The selected submatrix is diag(C,I_t), where C is the old selected submatrix, and its determinant is det C. This follows directly from the determinant permutation formula: nonzero terms must match each identity row with its equal identity column, leaving exactly the terms of det C. Hence D_s(P)⊆D_d(E).
4. To prove the reverse containment, fix a d-minor of E. Let S and T be the sets of identity-block indices appearing among its selected rows and columns. If some index lies in S but not T, its selected row is zero. If some index lies in T but not S, its selected column is zero. In either case the determinant is zero and belongs to D_s(P).
5. In the remaining case S=T. Set l=|S|, so l≤t. Permute the selected rows and columns to put their old indices first and to put their new indices last in the same increasing order. The matrix then has the form diag(C,I_l), where C is a (d−l)-minor of P. Row and column permutations multiply the determinant by signs, so the original determinant is a sign times det C. The determinant formula used in step 3 also proves det(diag(C,I_l))=det C. Since d=s+t and l≤t, we have d−l≥s; thus det C belongs to D_(d−l)(P)⊆D_s(P) by step 1. Multiplication by a sign preserves ideal membership.
6. Every generator of D_d(E) is therefore in D_s(P). Combine this with step 3. The case distinction in step 2 covers n=0, and the argument also covers t=0 and unavailable minor sizes: all claims about generators are universal over the existing embeddings, so an empty generating set requires no extra hypothesis.

## Key steps

1. Iterate successive-minor containment to compare arbitrary minor sizes.
2. If n≤r, select a suitable identity minor to make both ideals the whole ring.
3. If r<n, extend every old minor by the complete identity block.
4. Show mismatched selected identity indices force a zero row or column.
5. Reduce each remaining enlarged minor, up to sign, to an old minor of size at least n−r.
6. Combine the two ideal inclusions.

## Reference use

### local-project

Queries:
- `determinantal|fittingIdeal|fitting ideal|minor.*ideal|ideal.*minor`
- `det_mul|det_mul.*sum|det_succ|det_fromBlocks|det_submatrix|det_eq_zero_of`
- `fromBlocks_mulVec|mulVec_fromBlocks|mulVecLin|range_mulVecLin`
- `p05_pie_|minor_product|minor_descending|identity_stabilization|redundant_kernel`
- `git show ca1bb49d173a82f6c760dd27fdde39c92765501e:Submission.lean`
- `python3 /tmp/p05-pie-decomposition-eufao_g3/validate.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Data/Matrix/Block.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p05-pie-decomposition-eufao_g3/ChildTypes.lean`
- `/tmp/p05-pie-decomposition-eufao_g3/ChildTypes.lean.log`
- `/tmp/p05-pie-decomposition-eufao_g3/HeaderAbsence.lean`
- `/tmp/p05-pie-decomposition-eufao_g3/binding.json`

The searched algebra sources contain no matching determinantal-ideal or Fitting-ideal presentation-invariance theorem. Determinant/Basic.lean provides empty determinants, alternating determinant expansions, Laplace expansion, and block determinants; ToLin.lean identifies matrix images with column spans and matrix multiplication with composition; Data/Matrix/Block.lean supplies block multiplication formulas. Verified clean snapshot revisions 2fdd42759f4ab17640ac773289b521dd69d4b26e and db584cd6d46c92f209a44c0f1c829460d327499d, and all nine installed dependency pins. All four literal child types elaborate after import Submission. Anonymous Lean checks confirm matrix multiplication and identity-block semantics. Six inspected infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. Proposed names are unreserved across the checked 36-node DAG. Disposable compiler copies omit exactly policy-listed lines 10–11; the policy digest matches 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, Lean confirmed absence of all 13 targets, and binding.json records reversible original/build hashes. These are decomposition diagnostics, not comparator acceptance of child proofs.
