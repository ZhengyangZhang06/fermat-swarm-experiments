# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, W, and n satisfying the hypotheses. Let E be the projective cubic obtained by homogenizing the Weierstrass equation, and let O = [0:1:0]. Its affine points are nonsingular because Δ ≠ 0. The point O is its unique point at infinity and is nonsingular: in the homogenized equation the partial derivative with respect to the last coordinate is nonzero at O. Thus E is smooth. A repeated irreducible component would contradict smoothness. Distinct components of a reducible plane cubic intersect over an algebraically closed field, and their intersection would also be singular. Consequently E is integral. Its k-points identify with W.toAffine.Point, taking O to the identity constructor and each affine point to its coordinate constructor. Under this identification, the regular Weierstrass group law is the usual point-group law. We use the regularity of this law and the standard theorem that a nonconstant morphism of smooth projective integral curves is finite; these are the curve and Weierstrass facts in Silverman, The Arithmetic of Elliptic Curves, second edition (2009), Chapter II, §§2–3, and Chapter III, §§2–4.
2. On the chart around O put t = −X/Y and s = −Z/Y. The equation is s = t³ + a₁ts + a₂t²s + a₃s² + a₄ts² + a₆s³. The derivative with respect to s of the left side minus the right side is 1 at (0,0). Hence the completed local ring at O is k[[t]], with t a uniformizer. Successive comparison of coefficients determines s uniquely as a power series beginning with t³. This is also the local parameter construction of Silverman, Chapter IV, §1.
3. Write F(t₁,t₂) for the power series of addition at (O,O). The identities P + O = P and O + P = P imply F(t,0) = t and F(0,t) = t. Therefore F has zero constant term and linear part t₁ + t₂. Induction on j gives t([j]R) = j t(R) plus terms of order at least two for every positive integer j: it holds for j = 1, and composition with F adds one to the linear coefficient. In particular the coefficient n is nonzero in k because n > 0 and k has characteristic zero. Since [n] fixes O, a constant multiplication morphism would be constantly O and would have zero pullback of t. The displayed nonzero linear coefficient excludes this. Thus [n] is nonconstant.
4. Apply the finite-morphism theorem from step 1 to [n] : E → E. Its fiber over O is a finite scheme over k and consequently has finitely many k-points. Those points are exactly the points P satisfying [n]P = O. The group-compatible identification in step 1 therefore identifies this finite set with {P : W.toAffine.Point // n • P = 0}, proving the stated finiteness.

## Key steps

1. Identify the usual Weierstrass point group with the points of its smooth projective integral cubic.
2. Construct the uniformizer t at the identity using the equation in t and s.
3. Show that multiplication by n has nonzero linear term n in its local expansion.
4. Conclude that multiplication by n is nonconstant and finite, so its identity fiber is finite.

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
