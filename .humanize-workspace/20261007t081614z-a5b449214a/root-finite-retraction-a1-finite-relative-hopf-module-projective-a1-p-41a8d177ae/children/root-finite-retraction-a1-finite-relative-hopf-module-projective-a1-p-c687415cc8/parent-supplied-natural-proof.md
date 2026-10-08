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
