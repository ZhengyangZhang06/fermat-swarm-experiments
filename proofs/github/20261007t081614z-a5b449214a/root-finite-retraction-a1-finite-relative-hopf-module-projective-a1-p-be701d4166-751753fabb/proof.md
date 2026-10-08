# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.successive_minor_containment-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Denote the two determinantal ideals by D_(d+1)(P) and D_d(P). It suffices to put every generating (d+1)-minor in D_d(P); if there are no such minors the source ideal is zero.
2. Fix row and column embeddings ρ and γ from Fin(d+1), and put C=P[ρ,γ]. Expand det C along row 0. The term indexed by j∈Fin(d+1) is (-1)^j C(0,j) times the determinant obtained by deleting row 0 and column j.
3. The remaining row selection is i↦ρ(i+1), and the remaining column selection is γ composed with the increasing map from Fin d that skips j. Both maps are injective, being composites of injective maps. Thus each cofactor determinant is a generator of D_d(P). Each signed entry times that determinant belongs to D_d(P), as does their finite sum.
4. This proves the desired containment of spans. For d=0 the cofactor is the empty determinant 1 with its unique empty selections, so the same argument applies without a positivity assumption.

## Key steps

1. Reduce the ideal containment to a single generating minor.
2. Expand a (d+1)-determinant along its first row.
3. Identify each cofactor with a d-minor using composed embeddings.
4. Use closure under scalar multiplication and finite sums, including empty cofactors.

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
