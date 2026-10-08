# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.redundant_generator_relations-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write z=(x,y), meaning x(i)=z(inl i) and y(j)=z(inr j). For w=(u,v), block multiplication gives T w=(P u−A v,v), since the lower blocks of T are zero and the identity matrix. These are equations of vectors over R.
2. Suppose π(x)+ψ(y)=0. The hypothesis π(A y)=ψ(y) and linearity imply π(x+A y)=0. Thus x+A y belongs to ker π, which equals the image of P by hypothesis. Choose u with P u=x+A y and define w=(u,y). Step 1 gives T w=(P u−A y,y)=(x,y)=z. This proves the forward implication.
3. Conversely, suppose T w=z and write w=(u,v). Step 1 implies x=P u−A v and y=v. Since P u lies in the image of P=ker π, we have π(P u)=0. Consequently π(x)+ψ(y)=π(P u)−π(A v)+ψ(v)=0−ψ(v)+ψ(v)=0.
4. Both implications hold for every z. They use no surjectivity assumption and remain valid when any index set is empty, since the corresponding vector and matrix formulas use empty sums.

## Key steps

1. Compute T(u,v)=(Pu−Av,v).
2. Turn an enlarged relation into x+Ay∈ker(π).
3. Lift x+Ay through P and construct the preimage (u,y).
4. For the converse, use π(Pu)=0 and π(Av)=ψ(v) to cancel.

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
