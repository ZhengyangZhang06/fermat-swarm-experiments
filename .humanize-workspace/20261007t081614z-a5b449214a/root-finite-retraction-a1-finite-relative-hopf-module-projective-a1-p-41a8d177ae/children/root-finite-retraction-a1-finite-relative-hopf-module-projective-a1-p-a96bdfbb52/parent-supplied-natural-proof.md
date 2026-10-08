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
