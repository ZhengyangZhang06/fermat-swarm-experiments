<!-- theorem-id: fermat-p03/root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1.positive_nsmul_nonzero-a1 -->

## Theorem `Submission.p03_ptf_positive_nsmul_nonzero_c5b7b5ed_d6`

Let k be an algebraically closed field of characteristic zero with decidable equality, and let W be a Weierstrass curve over k with W.Δ ≠ 0. For every natural number n > 0, there exists P : W.toAffine.Point such that n • P ≠ 0, using the usual point-group operation and identity.

Node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1.positive_nsmul_nonzero-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/436

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p03_ptf_positive_nsmul_nonzero_c5b7b5ed_d6`

```lean
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k), W.Δ ≠ 0 → ∀ n : ℕ, 0 < n → ∃ P : W.toAffine.Point, n • P ≠ 0
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

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1.positive_nsmul_nonzero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, W, and n satisfying the hypotheses. Homogenize the Weierstrass equation to obtain the projective cubic E, with O = [0:1:0]. Nonzero discriminant makes every affine point nonsingular. Setting Z = 0 in the homogeneous equation gives X³ = 0, so O is the unique point at infinity. The partial derivative with respect to Z at O is 1, so O is nonsingular too. Thus E is smooth. A repeated component would have vanishing partial derivatives along that component. Distinct components would intersect over the algebraically closed field, and their intersection would also have vanishing partial derivatives. These possibilities contradict smoothness, so E is integral. Its k-points identify with W.toAffine.Point, with O corresponding to zero. The regular Weierstrass group law agrees with the usual point-group law. We use this standard regularity theorem as in Silverman, The Arithmetic of Elliptic Curves, second edition (2009), Chapter III, §§2–4. Consequently repeated addition defines a regular morphism [j] : E → E for every natural number j, fixing O.
2. On the chart Y ≠ 0 around O, put t = −X/Y and s = −Z/Y. The equation becomes s = t³ + a₁ts + a₂t²s + a₃s² + a₄ts² + a₆s³. The derivative with respect to s of the left side minus the right side is 1 at (0,0). The formal implicit-function theorem therefore identifies the completed local ring at O with k[[t]], with s represented by the unique series s(t) having constant coefficient zero and satisfying this equation. Coefficient comparison determines each coefficient of s from preceding coefficients: the first two coefficients vanish and the coefficient of t³ is 1. Thus s(t) starts with t³, and t is a uniformizer. This is the local-parameter construction of Silverman, Chapter IV, §1.
3. Complete the regular addition morphism at (O,O). Its pullback of t is a series F(t₁,t₂). The identities P + O = P and O + P = P imply F(t,0) = t and F(0,t) = t. Hence F has constant coefficient zero and linear part t₁ + t₂; every remaining term has total degree at least two.
4. Let H_j(t) be the completed pullback of t under [j]. We have H_1(t) = t, and the identity [j+1]R = [j]R + R gives H_(j+1)(t) = F(H_j(t),t). Inductively H_j has constant coefficient zero and linear coefficient j: substitution into every term of total degree at least two contributes only terms of degree at least two, while the linear part contributes H_j(t) + t. Therefore H_n(t) = n t plus terms of degree at least two. Since n > 0 and k has characteristic zero, its linear coefficient is nonzero, so H_n is nonzero.
5. Choose an affine open neighborhood U of O contained in the inverse image under [n] of the chart Y ≠ 0. The function g = t ∘ [n] is regular on U. Write U = Spec A. The algebra A is a finitely generated integral k-algebra because E is an integral curve of finite type. The image of g in the completed local ring at O is H_n, which is nonzero by step 4. Thus g is nonzero in A. Since A is a domain, A[g⁻¹] is a nonzero finitely generated k-algebra.
6. Choose a maximal ideal of A[g⁻¹]. Its residue field is a finitely generated k-algebra that is a field, hence a finite algebraic extension of k by Zariski's lemma. Algebraic closedness identifies that residue field with k. The resulting k-algebra homomorphism A[g⁻¹] → k defines a k-point R of U at which g is nonzero, because g is invertible in A[g⁻¹]. This is the weak Nullstellensatz argument; its algebraic ingredients occur in the pinned Mathlib/RingTheory/Jacobson/Ring.lean and Mathlib/RingTheory/Nullstellensatz.lean.
7. At this point, t([n]R) = g(R) ≠ 0, whereas t(O) = 0. Consequently [n]R ≠ O. Under the group-compatible identification E(k) ≃ W.toAffine.Point from step 1, R gives a point P satisfying n • P ≠ 0. This proves the required existence without any assumption about the size of a multiplication kernel.

## Key steps

1. Realize the usual point group on the smooth projective integral Weierstrass cubic.
2. Use the identity chart to identify the completed local ring with k[[t]].
3. Derive the linear part t₁ + t₂ of formal addition.
4. Inductively compute the nonzero linear coefficient n of multiplication by n.
5. Represent that nonzero completed germ by a nonzero regular function on an affine neighborhood.
6. Use the weak Nullstellensatz to obtain a k-point where the pullback is nonzero.
7. Transfer this point to W.toAffine.Point.

## Reference use

### local-project

Queries:
- `finite.*torsion|torsion.*finite|finite_nsmul|nsmul.*finite|nonconstant|formalGroup|formal group`
- `finite|Finite|nonconstant|Nonconstant|Scheme|uniformizer|PowerSeries|tangent`
- `nonconstant|Nonconstant|[Ff]ormal[Gg]roup|completed local|uniformizer|degree_nsmul|nsmul_degree`
- `inductive Point|instance.*AddCommGroup|equation_iff_nonsingular_of_Δ_ne_zero|def toAffine|equiv|Equiv|toProjective|nonsingular_zero`
- `weak|Zariski|IsAlgClosed|residue|Residue|finiteType`
- `class IsFinite|finite.*fiber|Finite.*fiber|isQuasiFinite`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions/Def_GaloisRep_Residual.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/RingTheory/Nullstellensatz.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/diagnostics/positive-kernel-d6-types-1ume4_n5/results.json`

The snapshot pins project 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Affine/Basic proves nonsingularity from nonzero discriminant; Affine/Point supplies the usual point group; Projective/Point supplies toAffineAddEquiv. Searches found no ready-made positive-torsion finiteness or multiplication-nonconstancy theorem in the inspected elliptic-curve sources. Def_GaloisRep_Residual assumes torsion cardinality, so it cannot supply this argument. Jacobson/Ring contains finite_of_finite_type_of_isJacobsonRing, supporting the closed-point argument; the scheme files supply general finite-morphism and finite-fiber infrastructure. Both proposed types elaborated after import Submission at frozen proof base adae8afec901619961ae1b5b1c73338837b271da. Instance probes confirmed nsmulBinRec and the identity constructor; checked types and point-group declarations depend only on propext, Classical.choice, and Quot.sound. Pinned repositories were clean, and searches of ten DAGs found no proposed-name collisions. The disposable compiler copy records the supplied policy digest, omission of exactly lines 10–11, reversible original/build hashes, and a successful absence probe for all 37 targets. Original sources and handoffs were unchanged. These are interface diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
