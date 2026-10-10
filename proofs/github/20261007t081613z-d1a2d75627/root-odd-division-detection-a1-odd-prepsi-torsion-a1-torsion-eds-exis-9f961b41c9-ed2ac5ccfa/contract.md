<!-- theorem-id: fermat-p03/root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1.finite_kernel_of_nsmul_nonzero-a1 -->

## Theorem `Submission.p03_ptf_finite_kernel_of_nsmul_nonzero_c5b7b5ed_d6`

Let k be an algebraically closed field with decidable equality, of arbitrary characteristic, and let W be a Weierstrass curve over k with W.Δ ≠ 0. For every natural number n, if there exists Q : W.toAffine.Point with n • Q ≠ 0, then the subtype {P : W.toAffine.Point // n • P = 0} is finite, using the usual point-group operation and identity.

Node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1.finite_kernel_of_nsmul_nonzero-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/436

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p03_ptf_finite_kernel_of_nsmul_nonzero_c5b7b5ed_d6`

```lean
∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k), W.Δ ≠ 0 → ∀ n : ℕ, (∃ P : W.toAffine.Point, n • P ≠ 0) → Finite {P : W.toAffine.Point // n • P = 0}
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
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.positive_torsion_finite-a1.finite_kernel_of_nsmul_nonzero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, W, n, and a point Q with n • Q ≠ 0. Let E be the projective cubic obtained by homogenizing the Weierstrass equation, and let O = [0:1:0]. Nonzero discriminant makes all affine points nonsingular. At infinity the equation forces X = 0, so O is the unique point there; the partial derivative with respect to Z at O is 1. Thus E is smooth. Repeated components would force vanishing partial derivatives along a component, and distinct components would intersect over k and force vanishing partial derivatives at their intersection. Smoothness excludes both possibilities. Hence E is a smooth projective integral curve. Its k-points identify with W.toAffine.Point, sending O to zero and respecting the regular Weierstrass group law. These curve and group-law facts hold in arbitrary characteristic; we use them as in Silverman, The Arithmetic of Elliptic Curves, second edition (2009), Chapter II, §§2–3, and Chapter III, §§2–4.
2. Repeated regular addition defines the multiplication morphism [n] : E → E. It sends O to O. The k-point corresponding to Q is sent to a point different from O, by the witness hypothesis and compatibility with the usual point-group law. Therefore [n] is nonconstant.
3. Apply the theorem that a nonconstant morphism between smooth projective integral curves is finite, as in Silverman, Chapter II, §§2–3. Its hypotheses hold for [n] by steps 1 and 2; no separability or characteristic-zero assumption is needed. Base change along the k-point O preserves finiteness. Consequently the scheme-theoretic fiber T = [n]⁻¹(O) is finite over k, so T = Spec B for a finite-dimensional commutative k-algebra B.
4. The set of k-points of Spec B is finite. To see this explicitly, its points correspond to k-algebra homomorphisms B → k. Each such map is surjective because it fixes k, and hence has a maximal kernel. Two such maps with the same kernel coincide: the quotient is one-dimensional over k, and a k-algebra map from that quotient to k is uniquely determined by its action on k. For any r distinct maps, their maximal kernels are pairwise comaximal, so the Chinese remainder theorem gives a surjective k-linear map B → kʳ. Therefore r ≤ dim_k B. There cannot be more than dim_k B distinct maps, proving that T(k) is finite. This argument also covers a nonreduced fiber.
5. By the defining fiber property, T(k) consists exactly of points R ∈ E(k) satisfying [n]R = O. Under the group-compatible identification in step 1, this condition is exactly n • P = 0. Thus T(k) is in bijection with {P : W.toAffine.Point // n • P = 0}. Transporting finiteness along this bijection proves the stated conclusion.

## Key steps

1. Construct the smooth projective integral cubic and identify its point group.
2. Use the nonzero-multiple witness and the fixed identity to prove multiplication is nonconstant.
3. Apply the finite-morphism theorem and base change to the identity fiber.
4. Bound the number of k-points of a finite k-algebra using maximal kernels and the Chinese remainder theorem.
5. Identify the finite fiber with the required torsion subtype.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/632

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
