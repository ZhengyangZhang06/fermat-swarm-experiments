<!-- theorem-id: fermat-p03/root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.torsion_card_recurrence-a1 -->

## Theorem `Submission.p03_tkc_torsion_card_recurrence_68cf3476_d5`

Let k be an algebraically closed field of characteristic zero with decidable equality, and let W be a Weierstrass curve over k with W.Δ ≠ 0. For each positive integer j write c_j = Nat.card {P : W.toAffine.Point // j • P = 0}. For every natural number m ≥ 2, one has c_(m+1) + c_(m−1) = 2c_m + 2.

Node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.torsion_card_recurrence-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/407

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/436

Decomposition children: None

## Lean problem

Declaration: `Submission.p03_tkc_torsion_card_recurrence_68cf3476_d5`

```lean
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k), W.Δ ≠ 0 → ∀ m : ℕ, 2 ≤ m → Nat.card {P : W.toAffine.Point // (m + 1) • P = 0} + Nat.card {P : W.toAffine.Point // (m - 1) • P = 0} = 2 * Nat.card {P : W.toAffine.Point // m • P = 0} + 2
```

### Frozen project context

`Fermat/Thm_WeierstrassCurve_galoisRep_ordinaryLineAt.lean` at `81f093181fd6c58dc887fcae5ec8b896996f1885` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_galoisRep_ordinaryLineAt.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_GaloisRep_Residual
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.galoisRep_ordinaryLineAt (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel)
    (hord : (p : ℤ) ∣ W.Δ ∨ ∃ i, 1 ≤ i ∧ i < (p ^ 2 - 1) / 2 ∧ ¬ (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ L : Submodule (ZMod p)
        (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p),
      L ≠ ⊤ ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ v : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
            (W.map (Int.castRingHom ℚ)) p σ v - v ∈ L := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.torsion_card_recurrence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, W, and m satisfying the hypotheses. Let E be the projective Weierstrass cubic with identity O. Nonzero discriminant makes every affine point smooth, and the unique point at infinity O is smooth. Smoothness excludes repeated components; distinct components would intersect over k and produce a singularity. Thus E is a smooth projective integral curve. Its k-points, with the regular Weierstrass group law, identify with W.toAffine.Point. For every positive j, the sibling theorem positive_torsion_finite gives finiteness of E[j] = {P : [j]P = O}. Define the reduced divisor K_j as the finite sum of these points, each with coefficient one. Since k is algebraically closed, each closed point has degree one, so deg K_j = c_j. We use the standard fact that a nonzero rational function on a smooth projective integral curve has principal divisor of degree zero. The curve and group-law facts used here are those of Silverman, The Arithmetic of Elliptic Curves, second edition (2009), Chapter II, §§2–3, Chapter III, §§2–4, and Chapter IV, §1.
2. At O use t = −x/y and s = −1/y. Their equation is s = t³ + a₁ts + a₂t²s + a₃s² + a₄ts² + a₆s³. Its derivative with respect to s at the origin is 1, so t is a uniformizer and coefficient recursion gives s = t³ plus higher-order terms. Therefore x = t/s has leading term t⁻². The power series F of addition has linear part t₁ + t₂, because F(t,0) = F(0,t) = t. Induction gives t([j]R) = j t(R) plus terms of order at least two. In particular every positive multiplication map is nonconstant in characteristic zero. Translation is an isomorphism, and [j](P+R) = [j]P + [j]R, so these expansions apply in the source parameter u = t(R) at every point P.
3. Define H = x ∘ [m] − x. This is a rational function, and at O it has leading term (m⁻² − 1)t⁻². The coefficient is nonzero: in characteristic zero, m ≥ 2 implies m ≠ 0 and m² − 1 ≠ 0. Thus H is nonzero and has order −2 at O.
4. Complete the square by setting z = y + (a₁x+a₃)/2 and G(X) = 4X³ + b₂X² + 2b₄X + b₆. The equation becomes z² = G(x)/4, and negation sends (x,z) to (x,−z). Consequently two affine points have the same x-coordinate exactly when they are equal or opposite. At an affine point Q with z(Q) ≠ 0, the nonzero partial derivative 2z(Q) makes x−x(Q) a uniformizer. At an affine point T with z(T) = 0, smoothness implies G′(x(T)) ≠ 0; here z is a uniformizer. Writing α = x(T), the equation gives x−α = (4/G′(α))z² plus higher-order terms. Since translations are local isomorphisms, these statements imply x(Q+R) = x(Q)+c u plus terms of order at least two when Q is not two-torsion, and x(T+R) = x(T)+c u² plus terms of order at least three when T is nonzero two-torsion, with c ≠ 0 in each case.
5. Let P ≠ O and suppose [m]P is affine. If [m]P = P and P is not two-torsion, use the linear expansion at P from step 4. In the source P+R the leading term of H is c(m−1)u, which is nonzero. Its order is therefore one. If [m]P = −P and P is not two-torsion, use x(−P+[m]R) = x(P−[m]R). The linear term of the first summand is −cmu, whereas that of x(P+R) is cu. Thus H has leading term −c(m+1)u and again order one. If P is nonzero two-torsion and [m]P = P, the quadratic expansion gives leading term c(m²−1)u², so the order is two. These coefficients are nonzero by characteristic zero and m ≥ 2. If [m]P is neither P nor −P, the two x-values differ, so H is regular and nonzero at P and has order zero.
6. If P ≠ O and [m]P = O, the first summand of H has leading term m⁻²u⁻², by step 2, while x is regular at P. Hence H has order −2 there. Together with step 3 this accounts for every pole and every point not covered by step 5.
7. These orders give div(H) = K_(m+1) + K_(m−1) − 2K_m − 2(O). Indeed, for P ≠ O the conditions [m]P = P and [m]P = −P are equivalent respectively to membership in E[m−1] and E[m+1]. If P is not two-torsion, they cannot both hold, so each simple zero contributes to exactly one of those divisors. If P is nonzero two-torsion and one condition holds, both hold, giving coefficient two. A nonidentity point with [m]P = O belongs to neither E[m−1] nor E[m+1], since [m−1]P = −P and [m+1]P = P are nonzero; its coefficient is −2. At O all three K-divisors have coefficient one, so the displayed right side has coefficient 1+1−2−2 = −2. All remaining coefficients vanish. Algebraic closedness ensures these k-point calculations cover every closed point, proving the divisor identity.
8. The integers m−1, m, and m+1 are positive, so all the divisors used are finite by step 1. Taking degrees in step 7 and using deg div(H) = 0 and deg(O) = 1 yields 0 = c_(m+1) + c_(m−1) − 2c_m − 2 as an integer equality. Rearranging gives c_(m+1) + c_(m−1) = 2c_m + 2. Injectivity of the natural-number inclusion into the integers gives precisely the asserted equality of natural cardinalities.

## Key steps

1. Use positive-torsion finiteness to form reduced kernel divisors whose degrees are the required cardinalities.
2. Compute the identity parameter and the linear term of multiplication.
3. Show H = x ∘ [m] − x is nonzero with a double pole at the identity.
4. Determine the linear or quadratic local behavior of x at affine points.
5. Compute all zeros and poles of H, distinguishing equal images, opposite images, two-torsion, and multiplication into the identity.
6. Establish div(H) = K_(m+1) + K_(m−1) − 2K_m − 2(O) coefficientwise.
7. Take degrees and transfer the resulting integer equality to natural cardinalities.

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


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
