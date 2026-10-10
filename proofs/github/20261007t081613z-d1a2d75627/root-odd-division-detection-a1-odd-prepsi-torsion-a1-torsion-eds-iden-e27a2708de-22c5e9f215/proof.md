# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.canonical_eds_recurrences-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.canonical_eds_recurrences-a1.canonical_odd_recurrence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k and W with the stated hypotheses. Work in the commutative ring A=W.toAffine.CoordinateRing. Let φ=q∘C, a_n=φ(W.preΨ' n), and b=φ(W.Ψ₂Sq). Both q and C are ring homomorphisms, so φ preserves multiplication, subtraction, powers, and 1. By definition, F(n)=a_n h when n is even and F(n)=a_n when n is odd.
2. The pinned identity WeierstrassCurve.ψ₂_sq is W.ψ₂²=C(W.Ψ₂Sq)+4W.toAffine.polynomial. Applying q and using q(W.toAffine.polynomial)=0 gives h²=b; this is also precisely CoordinateRing.mk_ψ₂_sq. Consequently h⁴=(h²)²=b².
3. Fix r∈ℕ with 2≤r and put m=r−2. Then r=m+2, m+1=r−1, m+3=r+1, and m+4=r+2. In particular, m and r have the same parity. The pinned identity preΨ'_odd at m states that W.preΨ'(2(m+2)+1) equals W.preΨ'(m+4)·W.preΨ'(m+2)³·(if m is even then W.Ψ₂Sq² else 1), minus W.preΨ'(m+1)·W.preΨ'(m+3)³·(if m is even then 1 else W.Ψ₂Sq²). Apply φ, use these index equalities, and commute factors in A. If r is even, this gives a_(2r+1)=b²a_(r+2)a_r³−a_(r−1)a_(r+1)³. If r is odd, it gives a_(2r+1)=a_(r+2)a_r³−b²a_(r−1)a_(r+1)³.
4. Suppose r is even. Then r+2 is even, while r−1 and r+1 are odd. Substituting the definition of F and using commutativity gives F(r+2)F(r)³−F(r−1)F(r+1)³=(a_(r+2)h)(a_r h)³−a_(r−1)a_(r+1)³=h⁴a_(r+2)a_r³−a_(r−1)a_(r+1)³. Replace h⁴ by b² and apply the even-r formula from step 3 to obtain a_(2r+1).
5. Suppose r is odd. Then r+2 is odd, while r−1 and r+1 are even. The same substitution gives F(r+2)F(r)³−F(r−1)F(r+1)³=a_(r+2)a_r³−(a_(r−1)h)(a_(r+1)h)³=a_(r+2)a_r³−h⁴a_(r−1)a_(r+1)³. Replace h⁴ by b² and apply the odd-r formula from step 3 to obtain a_(2r+1).
6. Every natural number r is even or odd, and 2r+1 is always odd. Therefore F(2r+1)=a_(2r+1), and steps 4–5 prove the asserted equality for every r≥2.

## Key steps

1. Define a_n and b using the composite ring homomorphism q∘C.
2. Use the coordinate-ring relation h²=b to obtain h⁴=b².
3. Reindex preΨ'_odd at m=r−2 and map it into the coordinate ring.
4. Expand the right-hand side separately for even and odd r, collecting four factors of h.
5. Substitute h⁴=b² and use that F(2r+1)=a_(2r+1).

## Reference use

### local-project

Queries:
- `preΨ'_even|preΨ'_odd|mk_ψ₂_sq|ψ₂_sq|preΨ'_zero|preΨ'_one|preΨ'_two|preΨ'_three|preΨ'_four`
- `def CoordinateRing|namespace CoordinateRing|def mk|abbrev mk|instance.*CommRing`
- `p03_eds_canonical_(odd|even)_recurrence_68cf3476_d4`
- `python3 /tmp/p03_canonical_recurrence_type_probe.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/diagnostics/canonical-recurrence-types-akmr8fr5/results.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/diagnostics/canonical-recurrence-types-akmr8fr5/TypesAfterSubmission.lean.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/diagnostics/canonical-recurrence-types-akmr8fr5/InstancesAfterSubmission.lean.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/diagnostics/canonical-recurrence-types-akmr8fr5/LibraryAxioms.lean.log`

The pinned project and mathlib revisions are 81f093181fd6c58dc887fcae5ec8b896996f1885 and db584cd6d46c92f209a44c0f1c829460d327499d. Basic.lean supplies the five initial identities, preΨ'_even, preΨ'_odd, and CoordinateRing.mk_ψ₂_sq. Point.lean defines the coordinate ring as AdjoinRoot and its quotient ring homomorphism. Both proposed types elaborated after literal import Submission using proof base 3e05ef5a1e0019d52ca3d0f58056550a77b706ef. Lean confirmed AdjoinRoot.instCommRing and its multiplication; the types and cited library lemmas depend only on propext, Classical.choice, and Quot.sound. Neither proposed name occurs in the ten inspected DAG registries. Snapshots and pinned dependencies were clean before and after checking. The diagnostic receipt records policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, exact omitted lines 10–11, reversible original/build hashes, and successful Lean absence checks for all 37 targets. Original sources were preserved. These are interface diagnostics, not comparator acceptance.
