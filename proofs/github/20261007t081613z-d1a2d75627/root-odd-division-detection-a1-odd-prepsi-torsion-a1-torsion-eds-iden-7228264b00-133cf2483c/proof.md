# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.canonical_eds_recurrences-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k and W as stated. Work in the commutative ring A, and write a_n=q(C(W.preΨ' n)) and b=q(C(W.Ψ₂Sq)). Thus F(n)=a_n h for even n and F(n)=a_n for odd n. The pinned identity WeierstrassCurve.ψ₂_sq says ψ₂²=C(Ψ₂Sq)+4W(X,Y). Applying q, which kills the defining equation, gives h²=b, equivalently the pinned CoordinateRing.mk_ψ₂_sq identity. Squaring gives h⁴=b².
2. Apply the ring homomorphism q∘C to WeierstrassCurve.preΨ'_zero, preΨ'_one, preΨ'_two, preΨ'_three, and preΨ'_four. These give a_0=0, a_1=a_2=1, a_3=q(C(W.Ψ₃)), and a_4=q(C(W.preΨ₄)). Since 0,2,4 are even and 1,3 are odd, the definition of F gives the five asserted initial values; for F(4), commute a_4 and h.
3. Fix r≥3 and put m=r−3. Natural subtraction is exact here: m+1=r−2, m+2=r−1, m+3=r, m+4=r+1, and m+5=r+2. Apply q∘C to the pinned identity preΨ'_even at m. Preservation of subtraction, multiplication and powers gives a_(2r)=a_(r−1)² a_r a_(r+2)−a_(r−2) a_r a_(r+1)². Factoring in the commutative ring A yields a_(2r)=a_r(a_(r+2)a_(r−1)²−a_(r−2)a_(r+1)²).
4. Fix r≥2 and put m=r−2. Then m+1=r−1, m+2=r, m+3=r+1, and m+4=r+2. Also m and r have the same parity because r=m+2. Apply q∘C to preΨ'_odd at m. The image of Ψ₂Sq² is b². Consequently, if r is even, a_(2r+1)=b²a_(r+2)a_r³−a_(r−1)a_(r+1)³; if r is odd, a_(2r+1)=a_(r+2)a_r³−b²a_(r−1)a_(r+1)³.
5. To prove the odd recurrence for F, fix r≥2. If r is even, r+2 is even and r−1,r+1 are odd, so F(r+2)F(r)³−F(r−1)F(r+1)³=h⁴a_(r+2)a_r³−a_(r−1)a_(r+1)³. Replace h⁴ by b² and use step 4 to obtain a_(2r+1). If r is odd, r+2 is odd and r−1,r+1 are even, so the same expression is a_(r+2)a_r³−h⁴a_(r−1)a_(r+1)³, again equal to a_(2r+1) by steps 1 and 4. Since 2r+1 is odd, a_(2r+1)=F(2r+1). This proves the odd recurrence in both cases.
6. To prove the even recurrence, fix r≥3 and set D=a_(r+2)a_(r−1)²−a_(r−2)a_(r+1)². If r is even, F(r)=a_r h, F(r+2)=a_(r+2)h, F(r−2)=a_(r−2)h, and F(r−1),F(r+1) have no h factor. Hence F(r)(F(r+2)F(r−1)²−F(r−2)F(r+1)²)=h²a_rD. If r is odd, F(r) and F(r±2) have no h factor, whereas each squared F(r±1) contributes h², giving the identical expression h²a_rD. By step 3 this is h²a_(2r). Since 2r is even, hF(2r)=h(a_(2r)h)=h²a_(2r), proving the required equality.
7. Steps 2, 5 and 6 establish every component of the stated conjunction. No cancellation, nonsingularity, or algebraic-closedness assumption was used.

## Key steps

1. Pass ψ₂²=C(Ψ₂Sq)+4W to the quotient to obtain h²=b and h⁴=b².
2. Map the five pinned preΨ' initial values and apply the parity definition of F.
3. Reindex preΨ'_even with r−3 and factor its image in the coordinate ring.
4. Reindex preΨ'_odd with r−2, preserving parity and mapping Ψ₂Sq² to b².
5. Expand the odd F recurrence in both parity cases and replace h⁴ by b².
6. Expand the even F recurrence in both parity cases; both sides equal h²a_(2r).

## Reference use

### local-project

Queries:
- `preΨ.|ψ₂|Ψ₂Sq`
- `namespace CoordinateRing|def basis|lemma.*basis|instance.*IsDomain|noncomputable.*basis|mk.*ne_zero|repr`
- `uniqu|ext|eq_of`
- `python3 /tmp/p03-eds-decomposition-check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
- `/tmp/p03-eds-decomposition-ubcfsypt/TypesAfterSubmission.lean.log`
- `/tmp/p03-eds-decomposition-ubcfsypt/result.json`

The pinned project revision is 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib revision is db584cd6d46c92f209a44c0f1c829460d327499d. DivisionPolynomial/Basic.lean supplies preΨ'_zero through preΨ'_four, preΨ'_even, preΨ'_odd, and CoordinateRing.mk_ψ₂_sq. Affine/Point.lean supplies the basis {1,Y}, smul_basis_eq_zero, and the coordinate-ring domain instance without a discriminant hypothesis; Affine/Basic.lean gives polynomialY with Y coefficient 2. No matching arbitrary-sequence uniqueness theorem was found in EllipticDivisibilitySequence.lean. Both proposed types elaborated after literal import Submission using the node's frozen proof-base context and the authorized disposable header copy. Lean confirmed the AdjoinRoot commutative-ring instance and CoordinateRing.instIsDomain; inspected library dependencies use only propext, Classical.choice, and Quot.sound. Pinned trees were clean before and after checking, and neither proposed name appeared in the ten inspected DAG registries. The diagnostic receipt records the required policy digest, exact omitted lines 10–11, reversible original/build hashes, and a successful absence probe for all 37 omitted targets. These are interface diagnostics, not comparator acceptance.
