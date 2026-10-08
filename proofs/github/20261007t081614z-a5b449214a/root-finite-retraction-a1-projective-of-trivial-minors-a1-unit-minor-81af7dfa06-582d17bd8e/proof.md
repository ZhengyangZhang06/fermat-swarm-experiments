# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.inner_inverse_of_minors-a1`
- Child DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.inner_inverse_of_minors-a1.inner_inverse_of_reconstruction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write L=P.submatrix id cols and H=P.submatrix rows id, so the hypothesis is P=LTH. Define the p-by-d matrix U by U(s,a)=1 if s=cols(a) and U(s,a)=0 otherwise. Define the d-by-n matrix V by V(b,t)=1 if rows(b)=t and V(b,t)=0 otherwise. Equivalently, U and V are the corresponding submatrices of the p-by-p and n-by-n identity matrices. Put Q=UTV, a p-by-n matrix.
2. For each i in Fin n and a in Fin d, matrix multiplication gives (PU)(i,a)=sum over s in Fin p of P(i,s)U(s,a). Only s=cols(a) can contribute, and its contribution is P(i,cols(a)); hence PU=L. Similarly, for b in Fin d and j in Fin p, (VP)(b,j)=sum over t in Fin n of V(b,t)P(t,j)=P(rows(b),j). Thus VP=H. These finite-sum equalities require no cancellation and hold in a zero ring as well.
3. By associativity of matrix multiplication, PQP=P(UTV)P=(PU)T(VP)=LTH=P. Therefore the constructed Q witnesses the claimed existence.
4. If d=0, UTV is the zero matrix because its intermediate sums are empty, and the assumed reconstruction already gives P=0. Empty ambient dimensions make the relevant entrywise equalities vacuous. Thus the construction covers all stated dimensions without extra assumptions.

## Key steps

1. Construct selection matrices U and V from identity matrices and define Q=UTV.
2. Evaluate finite sums to prove PU=P.submatrix id cols and VP=P.submatrix rows id.
3. Use associativity and the assumed reconstruction to derive PQP=P.
4. Verify that the same construction covers empty dimensions and zero rings.

## Reference use

### local-project

Queries:
- `inner.inverse|generalized.inverse|unit_minor|minor_reconstruction|supported_inner_inverse`
- `theorem (det_fromBlocks|mul_nonsing_inv|nonsing_inv_mul)|fromBlocks_mul|submatrix_mul_equiv`
- `toMatrix|submatrix.*mul|mul.*submatrix`
- `theorem (mul_adjugate|adjugate_mul)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Data/Matrix/Block.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-a44555b14f/decomposition-inner-inverse-0nwgeq0a/CheckInterfaces.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-a44555b14f/decomposition-inner-inverse-0nwgeq0a/interface-report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-a44555b14f/decomposition-inner-inverse-0nwgeq0a/header-receipt.json`

The project search found no matching reconstruction or inner-inverse helper. Pinned mathlib supplies adjugate identities, both nonsingular-inverse identities, Schur-complement determinants, selection-matrix identities, and block multiplication. Both snapshots and all nine compiler dependencies matched their clean pins. Both proposed types elaborate after import Submission; additional Lean checks verify matrix multiplication, the nonsingular inverse, and conditional assembly of the exact parent type. Both names are absent from the imported environment and all ten local DAG registries. Eleven inspected infrastructure declarations have transitive axiom closures contained in propext, Classical.choice, and Quot.sound. Diagnostics are bound to Git base 04398660623bce240a72f088ddc4afbad23db1f8. The private compiler copy follows policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: exactly lines 10–11 are omitted, all 13 targets were checked absent by Lean, and reversible original/build hashes are recorded. Concurrent integration was recorded separately; the frozen contract, problem, handoff, and Submission header remain unchanged. These are interface diagnostics, not comparator acceptance of the proposed theorems.
