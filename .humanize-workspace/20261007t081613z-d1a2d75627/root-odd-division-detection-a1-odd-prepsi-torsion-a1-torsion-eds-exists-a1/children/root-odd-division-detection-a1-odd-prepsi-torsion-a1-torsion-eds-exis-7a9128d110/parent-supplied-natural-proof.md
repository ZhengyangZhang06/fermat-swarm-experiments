# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_sum_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, W, n and S satisfying the hypotheses, and write E for the additive group W.toAffine.Point. Apply the sibling theorem p03_eds_torsion_kernel_card_68cf3476_d4 with the same k and W and with index 2. Its hypotheses hold because 2 > 0. Consequently E[2] = {P ∈ E : 2 • P = 0} is finite and has exactly four elements.
2. Negation preserves S: if n • P = 0, then n • (−P) = −(n • P) = 0. It is an involution. Every orbit that is not a fixed point is the two-element set {P,−P}, whose sum is zero. Thus the sum of S equals the sum of its fixed-point subset F = {P ∈ S : P = −P}. Explicitly, this reduction follows by finite induction: whenever a nonfixed P remains, remove the distinct pair P and −P; the remainder is still stable under negation, and removing the pair does not change the sum. The process terminates with F. In an additive group, P = −P is equivalent to 2 • P = 0.
3. Suppose n is odd, and write n = 2r + 1. For P ∈ F, both n • P and 2 • P are zero. Therefore 0 = n • P = r • (2 • P) + P = P. Conversely, zero belongs to S and is fixed by negation. Hence F consists only of zero, and its sum is zero.
4. Suppose n is even, and write n = 2r. Every point P of E[2] satisfies n • P = r • (2 • P) = 0, so it belongs to S and to F. The reverse inclusion follows from the definition of F. Thus F consists of all four elements of E[2]. This set is an additive subgroup, because multiplication by 2 is an additive homomorphism.
5. Choose distinct nonzero elements U and V of E[2]; they exist because E[2] has four elements, only one of which is zero. The element U + V also belongs to E[2]. It is nonzero: otherwise V = −U = U, contrary to their distinctness. It differs from U and V by cancellation and the nonvanishing of V and U respectively. Therefore the four elements 0, U, V and U + V are distinct and exhaust E[2]. Their sum is 0 + U + V + (U + V) = 2 • U + 2 • V = 0.
6. Every natural number is odd or even. Steps 3–5 therefore show that the fixed-point sum is zero in all cases. Combining this with step 2 gives S.sum (fun P => P) = 0, as required.

## Key steps

1. Specialize the kernel-cardinality sibling to obtain exactly four two-torsion points.
2. Cancel all nonfixed pairs under the negation involution on S.
3. For odd n, show that a point killed by both n and 2 must be zero.
4. For even n, identify the fixed-point subset with the whole two-torsion subgroup.
5. Enumerate that subgroup as 0, U, V, U + V and compute its sum as zero.
6. Conclude that the sum over S is zero in both parity cases.

## Reference use

### local-project

Queries:
- `ψ_|Ψ_|ψ₂|preΨ₄|XYIdeal|ordinaryLineAt|division.*polynomial|DivisionPolynomial`
- `Nat.card.*torsion|card.*torsionBy|sum.*(invol|neg|orderOf)|sum.*eq_zero`
- `namespace Point|deriving|instAddCommGroup|instAddGroup|neg_some|two_nsmul|Nonsingular`
- `twoTorsionPolynomial_discr|twoTorsionPolynomial|b_relation`
- `p03_eds_torsion_kernel_card_68cf3476_d4|p03_eds_torsion_kernel_sum_68cf3476_d4`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p03_eds_geometric_split_mce1cixa/ChildTypes.lean`
- `/tmp/p03_eds_geometric_split_mce1cixa/HeaderAbsence.lean`
- `/tmp/p03_eds_geometric_split_mce1cixa/InstanceAxioms.log`
- `/tmp/p03_eds_geometric_split_mce1cixa/receipt.json`

The snapshot records project 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; the compiler's mathlib checkout matched and was clean. DivisionPolynomial/Basic.lean already supplies the canonical initial values and recurrences. Affine/Basic.lean supplies nonsingularity from nonzero discriminant; Affine/Point.lean supplies the intended point group, negation and equality-of-x-coordinate criterion. Weierstrass.lean proves that the two-torsion cubic has discriminant 16Δ. The targeted torsion-cardinality and torsion-sum search found no relevant theorem in the searched elliptic-curve and finite-abelian-group modules. The DAG already reserves recurrence uniqueness in another branch; neither proposed identifier was reserved. Both exact child types elaborated after import Submission using a disposable copy of the parent's frozen proof base. Lean confirmed the canonical point-group instances and definitionally identified natural scalar multiplication with nsmulBinRec. The inspected library declarations have only propext, Classical.choice and Quot.sound as transitive axioms. Policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 matched; only listed lines 10 and 11 were omitted, all 37 targets were checked absent under the frozen imports, and byte-exact restoration and dependency-source checks passed. These are interface diagnostics, not comparator acceptance of either proposed theorem.
