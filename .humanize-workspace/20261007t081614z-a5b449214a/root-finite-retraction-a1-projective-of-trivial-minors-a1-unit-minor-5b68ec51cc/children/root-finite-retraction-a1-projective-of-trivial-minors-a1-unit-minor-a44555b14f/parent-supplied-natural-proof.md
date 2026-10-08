# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1`
- Child DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.inner_inverse_of_minors-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let I be the row indices not in the image of rows, and J the column indices not in the image of cols. The maps e_r:Fin d ⊕ I → Fin n and e_c:Fin d ⊕ J → Fin p that use the given embeddings on the left and inclusion on the right are bijective: an index in the selected image has a unique selected preimage by injectivity, and every other index has a unique complementary preimage. Reindex P by these bijections to obtain A=[[B,C],[D,E]], where B=P.submatrix rows cols.
2. Since det B is a unit, choose a in R with a det B=det B a=1, and put B'=a adj(B). Cofactor expansion gives B adj(B)=adj(B)B=det(B)I: diagonal entries are determinant expansions, while off-diagonal entries expand determinants with a repeated row or column and vanish. Hence BB'=B'B=I, also for d=0.
3. For i in I and j in J, append i and j to the selected row and column lists. Because these indices are outside the selected images, these are embeddings from Fin(d+1). The resulting determinant is zero by hypothesis. Its matrix has blocks [[B,C_j],[D_i,E_ij]]. Subtract from its last row the sum of its first d rows with coefficient row D_i B'. By determinant multilinearity, each correction term has a row repeated among the unchanged first d rows and contributes zero, so this subtraction preserves the determinant. The last row becomes [0,E_ij-D_i B'C_j], because B'B=I. Expansion along that row gives det B times E_ij-D_i B'C_j; the last diagonal cofactor has positive sign. Multiplying the resulting zero equality by a gives E_ij=D_i B'C_j. Thus E=DB'C. If I or J is empty this equality is vacuous.
4. Let Q0 be the matrix with row indices Fin d ⊕ J and column indices Fin d ⊕ I whose upper-left block is B' and whose other three blocks are zero. Block multiplication gives A Q0 A=[[BB'B,BB'C],[DB'B,DB'C]]=[[B,C],[D,E]]=A, using both inverse identities and Step 3.
5. Transport Q0 back to a p-by-n matrix Q by prescribing Q(e_c(v),e_r(u))=Q0(v,u). Reindexing the finite sums defining matrix multiplication gives (PQP)(e_r(u),e_c(v))=(A Q0 A)(u,v)=A(u,v)=P(e_r(u),e_c(v)). The two bijections are surjective, so PQP=P.
6. No cancellation of a nonzero scalar was used: only multiplication by the inverse of a unit. For d=0, the bordered determinants are the entries of P, so Step 3 says P=0 and the construction gives Q=0. Empty complements cause no extra obligation. Thus the argument also covers zero rings and all empty dimensions.

## Key steps

1. Reindex the selected rows and columns into an initial square block.
2. Invert the selected block using its unit determinant and the adjugate identities.
3. Use bordered minors and determinant-preserving row subtraction to prove E=DB'C.
4. Construct the block matrix Q0 with sole nonzero block B' and verify A Q0 A=A.
5. Transport Q0 through the coordinate bijections to obtain PQP=P.
6. Check that empty dimensions and zero rings require no additional assumptions.

## Reference use

### local-project

Queries:
- `inner.inverse|generalized.inverse|unit_minor|unit.*minor|split.*minor`
- `det_fromBlocks|isUnit_iff_isUnit_det|mul_adjugate|adjugate_mul|det_updateRow|det_succ`
- `mulVecLin_mul|mulVecLin.*comp|def mulVecLin|def liftOfSurjective|liftOfSurjective`
- `range.*[Cc]ompl|exists.*[Rr]ight[Ii]nverse|ofBijective|liftQ|isIdempotentElem_iff`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean HeaderPolicyCheck.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean CheckAll.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Projection.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-5b68ec51cc/decomposition-ums-diagnostics-y5c5gqal/build/CheckAll.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-5b68ec51cc/decomposition-ums-diagnostics-y5c5gqal/interface-report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-5b68ec51cc/decomposition-ums-diagnostics-y5c5gqal/name-audit.json`

The targeted project search found no matching inner-inverse or unit-minor splitting theorem. Pinned mathlib supplies adjugate identities, Schur-complement determinants, Matrix.mulVecLin_mul, and quotient/projection infrastructure. Both snapshots and all nine compiler dependencies matched their clean pins. Both literal child types elaborate after import Submission; anonymous checks verify genuine matrix multiplication by its finite-sum formula, scalar IsUnit semantics, and conditional assembly of the exact frozen parent. Six inspected infrastructure declarations have transitive axiom closures contained in propext, Classical.choice, and Quot.sound. Proposed names are absent from the imported environment, current Submission, and ten DAG registries. Private compiler copies omit exactly lines 10–11 under policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; Lean confirms all 13 targets absent. The receipt records exact omissions and reversible original/build hashes. The frozen contract, problem record, and handoff remain unchanged. These are interface diagnostics; proof acceptance still requires the configured comparator and independent review.
