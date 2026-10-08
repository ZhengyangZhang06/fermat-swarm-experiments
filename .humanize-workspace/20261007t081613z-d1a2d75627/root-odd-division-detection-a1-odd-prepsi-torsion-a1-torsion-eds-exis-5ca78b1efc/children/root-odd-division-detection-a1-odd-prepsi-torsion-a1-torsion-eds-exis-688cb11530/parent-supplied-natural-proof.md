# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.two_torsion_card-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k and W satisfying the hypotheses. Since Δ ≠ 0, every affine solution of the Weierstrass equation is nonsingular and represents a point of W.toAffine.Point. Its remaining point is the identity O. In an additive group, 2 • P = 0 is equivalent to P = −P, by adding −P to P + P = 0 and conversely adding P to P = −P.
2. Characteristic zero makes 2 and 4 invertible. Set z = y + (a₁x + a₃)/2 and G(X) = 4X³ + b₂X² + 2b₄X + b₆, where b₂ = a₁² + 4a₂, b₄ = a₁a₃ + 2a₄, and b₆ = a₃² + 4a₆. Expanding the square shows that the Weierstrass equation is equivalent to z² = G(x)/4. The coordinate transformation is invertible, with y = z − (a₁x + a₃)/2. The usual negation formula (x,y) ↦ (x,−y−a₁x−a₃) becomes (x,z) ↦ (x,−z).
3. The polynomial G has degree three because its leading coefficient 4 is nonzero. It has no repeated root: if α were repeated, then G(α) = G′(α) = 0. The point (α,0) would satisfy z² − G(x)/4 = 0, and both partial derivatives, 2z and −G′(x)/4, would vanish there. The invertible coordinate transformation would then give a singular affine point of W, contradicting Δ ≠ 0. Algebraic closedness therefore gives exactly three distinct roots of G.
4. An affine point is fixed by negation exactly when z = −z, equivalently z = 0. Such points correspond bijectively to the three roots α of G, by α ↦ (α,−(a₁α+a₃)/2). Each is a valid nonsingular affine point, and different roots give different points. By step 1 these are exactly the nonidentity two-torsion points. The identity O is itself two-torsion and is distinct from all affine points. Thus the two-torsion subtype is in bijection with a singleton disjointly joined to a three-element set, so it is finite and its Nat.card is 1 + 3 = 4.

## Key steps

1. Express two-torsion as the fixed points of negation.
2. Complete the square so negation changes z to −z.
3. Use nonsingularity to show that the resulting cubic has three distinct roots.
4. Count one affine fixed point per root and add the identity.

## Reference use

### local-project

Queries:
- `torsion_kernel|Nat.card.*torsionBy|Finite.*n •|Nat.card.*n •|torsion.*card.*square|card.*torsion.*square`
- `torsion.*(finite|card)|finite.*torsion|card.*torsion|degree_nsmul|nsmul_degree|mul.*[Ee]tale|parallelogram|card.*nsmul`
- `twoTorsionPolynomial|two_torsion|twoTorsion`
- `equation_iff_nonsingular|nonsingular_of_Δ|nonsingular_of_delta|def negY|nonsingular_iff|nonsingular.*Δ`
- `degree.*principal|principal.*degree|HasPrincipalDivisors|degree_pullback`
- `python3 /tmp/p03-tkc-typecheck.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions/Def_GaloisRep_Residual.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/diagnostics/torsion-cardinality-types-ahgv6cn7/results.json`

The snapshot pins project 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Point.lean includes the identity constructor, affine negation, and the usual AddCommGroup instance; Basic.lean proves equation_iff_nonsingular_of_Δ_ne_zero. Weierstrass.lean defines the cubic with coefficients (4,b₂,2b₄,b₆) and proves its discriminant is 16Δ; DivisionPolynomial/Basic.lean supplies the corresponding square identity. Searches found no ready-made positive-torsion finiteness, square-cardinality, or cardinality-recurrence theorem. Def_GaloisRep_Residual.lean assumes the torsion cardinality; HasPrincipalDivisors and FundamentalIdentity likewise require their mathematical hypotheses and do not discharge this proof automatically. All three proposed types elaborated after import Submission at the node's frozen proof base. Instance probes confirmed the standard natural-number action and identity. Checked library declarations and type expressions use only propext, Classical.choice, and Quot.sound. Pinned dependencies were clean; ten DAGs contained no proposed-name collisions. The diagnostic records the matching policy digest, reversible omission of exactly lines 10–11, original/build hashes, and a successful Lean absence probe for all 37 targets. These are interface diagnostics, not comparator acceptance.
