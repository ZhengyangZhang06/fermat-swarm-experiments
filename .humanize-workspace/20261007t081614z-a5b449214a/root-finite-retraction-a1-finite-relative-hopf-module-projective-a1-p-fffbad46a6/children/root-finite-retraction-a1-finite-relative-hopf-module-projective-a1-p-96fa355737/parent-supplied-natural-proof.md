# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.extend_minor-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put C=P[rows,cols]. Identify Fin(s+t) with Fin s ⊕ Fin t by sending an index i<s to the left index i and an index i≥s to the right index i−s. This is a bijection; its inverse sends a left index a to a and a right index b to s+b.
2. Define rows' on the first s positions by rows'(i)=inl(rows(i)), and on the last t positions by rows'(s+j)=inr(j). Define cols' in the same way using cols on the first s positions. Each map is injective: equality between different blocks is impossible, equality within the old block reduces to injectivity of the original embedding, and equality within the new block reduces to equality of the indices. Thus both maps are the required embeddings.
3. After simultaneous reindexing of rows and columns by the bijection in step 1, E[rows',cols'] is diag(C,I_t). Its old-old entries are those of C, its two off-diagonal blocks are zero, and its new-new entry at (i,j) is 1 if i=j and 0 otherwise. Simultaneous reindexing preserves determinant: conjugating permutations in the determinant sum preserves their signs and simply reindexes their products.
4. In the determinant expansion of diag(C,I_t), every term whose permutation fails to fix some new index has a zero entry from that identity row. The remaining permutations fix every new index and restrict bijectively to permutations of the s old indices. Their signs equal the signs of these restrictions, and all new diagonal factors are 1. The remaining sum is therefore det C.
5. Steps 3 and 4 give det(E[rows',cols'])=det C, proving the assertion with the embeddings from step 2. The argument includes s=0 and t=0 because empty products are 1 and the empty index set has one permutation.

## Key steps

1. Construct the canonical bijection Fin(s+t) ≃ Fin s ⊕ Fin t.
2. Append every identity-block index to each original embedding and prove injectivity.
3. Simultaneously reindex the selected matrix as diag(C,I_t).
4. Use the determinant permutation formula to remove the fixed identity indices and obtain det C.

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
