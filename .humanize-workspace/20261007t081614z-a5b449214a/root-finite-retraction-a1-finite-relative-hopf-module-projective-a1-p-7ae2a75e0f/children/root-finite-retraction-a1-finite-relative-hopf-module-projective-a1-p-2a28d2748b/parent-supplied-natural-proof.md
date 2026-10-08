# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.minor_product_containment-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. For a matrix C write D_d(C) for the ideal spanned by the determinants of submatrices selected by embeddings from Fin d into its row and column sets. When d=0, the unique empty selections give determinant 1, so each of the three ideals is the whole ring and the assertion follows.
2. Suppose d>0. Fix embeddings ρ:Fin d→ι and γ:Fin d→ν. The j-th column of (AB)[ρ,γ] is the sum, over k∈κ, of B(k,γ(j)) times the column i↦A(ρ(i),k). Multilinearity therefore expresses its determinant as the sum over all functions f:Fin d→κ of (the product over j of B(f(j),γ(j))) times det(A[ρ,f]).
3. If f is not injective, two columns of A[ρ,f] coincide and its determinant is zero by alternation. If f is injective, it defines a column embedding and det(A[ρ,f]) is a generator of D_d(A). Each term, and hence the selected determinant of AB, belongs to D_d(A).
4. Independently expand in rows: row i of (AB)[ρ,γ] is the sum over k∈κ of A(ρ(i),k) times the row j↦B(k,γ(j)). Its determinant is the sum over g:Fin d→κ of (the product over i of A(ρ(i),g(i))) times det(B[g,γ]). Repeated values of g give equal rows and zero determinant; injective g give generators of D_d(B). Thus the same determinant belongs to D_d(B).
5. Every generating minor of AB belongs to both ideals, so its span is contained in their intersection. If either outer embedding does not exist, there are no generating minors and the containment is immediate; an empty middle index set is already covered by the finite-sum expansions.

## Key steps

1. Handle d=0 using the empty determinant.
2. Expand each selected product minor multilinearly in columns.
3. Discard repeated columns and place all remaining terms in D_d(A).
4. Expand in rows and place all terms in D_d(B).
5. Pass from the generating minors to their ideal span.

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
