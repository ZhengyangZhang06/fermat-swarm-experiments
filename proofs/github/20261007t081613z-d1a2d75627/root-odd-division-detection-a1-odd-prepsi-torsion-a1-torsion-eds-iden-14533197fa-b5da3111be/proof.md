# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.eds_recurrence_uniqueness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix R,h,f,g and all the stated hypotheses. Prove f(n)=g(n) by strong induction on n. At the induction step, assume f(j)=g(j) for every natural j<n.
2. If n≤4, the asserted equality is exactly the initial-agreement hypothesis. Otherwise n≥5.
3. Suppose n is odd. Write n=2r+1. The bound n≥5 implies r≥2. Since r+2<2r+1, all four indices r−1,r,r+1,r+2 are less than n. The induction hypothesis therefore identifies f and g at every index appearing on the right side of the odd recurrence. Apply that recurrence first to f, substitute these four equalities, and apply the recurrence for g in reverse. This gives f(n)=f(r+2)f(r)³−f(r−1)f(r+1)³=g(r+2)g(r)³−g(r−1)g(r+1)³=g(n).
4. Suppose n is even. Write n=2r. Since n≥5 and n is even, r≥3. The inequality r+2<2r shows that every index r−2,r−1,r,r+1,r+2 is less than n. Substituting the induction equalities into the two even recurrences gives h f(n)=f(r)(f(r+2)f(r−1)²−f(r−2)f(r+1)²)=g(r)(g(r+2)g(r−1)²−g(r−2)g(r+1)²)=h g(n). Thus h(f(n)−g(n))=0. Because R has no zero divisors and h≠0, f(n)−g(n)=0, hence f(n)=g(n).
5. Every natural n is covered by the base case or one of the two parity cases. Strong induction proves f(n)=g(n) for all n.

## Key steps

1. Use strong induction on the sequence index.
2. Discharge indices 0 through 4 using initial agreement.
3. For n=2r+1≥5, all recurrence indices are smaller; substitute induction equalities into the odd recurrence.
4. For n=2r≥6, all recurrence indices are smaller; the even recurrences give h f(n)=h g(n).
5. Cancel the nonzero factor h in the integral domain and conclude the induction.

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
