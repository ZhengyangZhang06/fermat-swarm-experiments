# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.canonical_eds_recurrences-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.canonical_eds_recurrences-a1.canonical_even_recurrence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k and W with the stated hypotheses. Work in the commutative ring A=W.toAffine.CoordinateRing. Let φ=q∘C and a_n=φ(W.preΨ' n). The map φ is a ring homomorphism. Thus F(n)=a_n h for even n and F(n)=a_n for odd n.
2. Fix r∈ℕ with 3≤r and set m=r−3. Natural subtraction is exact here: m+1=r−2, m+2=r−1, m+3=r, m+4=r+1, and m+5=r+2. The pinned identity preΨ'_even at m states that W.preΨ'(2(m+3))=W.preΨ'(m+2)²·W.preΨ'(m+3)·W.preΨ'(m+5)−W.preΨ'(m+1)·W.preΨ'(m+3)·W.preΨ'(m+4)². Apply φ, which preserves products, subtraction, and squares, and substitute the index equalities. This yields a_(2r)=a_(r−1)²a_r a_(r+2)−a_(r−2)a_r a_(r+1)².
3. Put D=a_(r+2)a_(r−1)²−a_(r−2)a_(r+1)². Commutativity and distributivity in A transform the equality from step 2 into a_(2r)=a_rD.
4. Suppose r is even. Then r−2 and r+2 are even, while r−1 and r+1 are odd. The required right-hand side therefore equals (a_rh)((a_(r+2)h)a_(r−1)²−(a_(r−2)h)a_(r+1)²). Factoring h from the bracket and commuting factors gives h²a_rD.
5. Suppose r is odd. Then r−2 and r+2 are odd, while r−1 and r+1 are even. The required right-hand side equals a_r(a_(r+2)(a_(r−1)h)²−a_(r−2)(a_(r+1)h)²). Expanding the squares and factoring h² gives h²a_rD again.
6. The two parity cases exhaust all r. By step 3 their common result is h²a_(2r). Since 2r is even, the required left-hand side is hF(2r)=h(a_(2r)h)=h²a_(2r). Hence the two sides are equal for every r≥3. No cancellation of h is required.

## Key steps

1. Define a_n using the composite ring homomorphism q∘C.
2. Reindex preΨ'_even at m=r−3 and map its identity into the coordinate ring.
3. Factor the mapped identity as a_(2r)=a_rD.
4. In each parity case, expand the recurrence's right-hand side to h²a_rD.
5. Use a_(2r)=a_rD and the evenness of 2r to identify both sides with h²a_(2r).

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
