# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.inner_inverse_of_minors-a1`
- Child DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.inner_inverse_of_minors-a1.minor_reconstruction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define B=P.submatrix rows cols, L=P.submatrix id cols, H=P.submatrix rows id, and T=B⁻¹, the nonsingular matrix inverse. Thus L(i,b)=P(i,cols(b)) and H(a,j)=P(rows(a),j). We will prove P(i,j)=(LTH)(i,j) for every i and j.
2. Since det B is a unit, its ring inverse a satisfies a det B=det B a=1. By the definition of the nonsingular matrix inverse, T=a adj(B). Cofactor expansion gives B adj(B)=adj(B)B=(det B)I: the diagonal entries are determinant expansions, and an off-diagonal entry is the determinant of a matrix with a repeated row or column, hence zero. Therefore BT=TB=I. These identities also hold for the empty square matrix.
3. If i=rows(s) for some s, then row i of L is row s of B. Consequently row i of LT is row s of BT=I, so (LTH)(i,j)=H(s,j)=P(i,j). This settles every selected row.
4. If j=cols(t) for some t, column j of H is column t of B. Therefore column j of TH is column t of TB=I, so (LTH)(i,j)=L(i,t)=P(i,j). This settles every selected column, including its intersections with selected rows.
5. It remains to consider i outside the image of rows and j outside the image of cols. Append i and j as the last entries of the respective selected lists, preserving the order of the original d entries. Each resulting map from Fin(d+1) is injective: the first d entries are distinct by the given embedding, and the last entry lies outside their image. The corresponding bordered matrix M has upper-left block B, last column above its corner c with c(a)=P(rows(a),j), last row before its corner r with r(b)=P(i,cols(b)), and corner e=P(i,j). Its determinant is zero by the larger-minor hypothesis.
6. Let w=rT. Replace the last row of M by that row minus the sum, over a in Fin d, of w(a) times row a. Determinant linearity in the last row expresses the change as a sum of determinants with the last row equal to an unchanged earlier row; each vanishes by alternation. Thus the determinant is unchanged. The first d entries of the new last row are r-wB=r-rTB=0, and its corner is e-wc=e-rTc. Expanding along this last row gives det M=(det B)(e-rTc): the last diagonal cofactor has sign (-1)^(2d)=1 and minor B. Since det M=0, multiplying by a yields e-rTc=0. Hence P(i,j)=rTc=(LTH)(i,j).
7. The selected-row, selected-column, and complementary cases cover all indices, so entrywise equality proves P=LTH. For d=0 the sums are empty, det B=1, and the bordered determinant is P(i,j), so the same argument proves P=0. If either ambient index type is empty, entrywise equality is vacuous. Only inversion of a unit was used, so zero rings require no exception.

## Key steps

1. Use the unit determinant and adjugate formula to establish both inverse identities for B⁻¹.
2. Prove reconstruction on selected rows using BB⁻¹=I.
3. Prove reconstruction on selected columns using B⁻¹B=I.
4. Append complementary indices to obtain a vanishing bordered determinant.
5. Subtract rB⁻¹ times the selected rows and expand the determinant to obtain e=rB⁻¹c.
6. Combine all entry cases, including empty dimensions and zero rings.

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
