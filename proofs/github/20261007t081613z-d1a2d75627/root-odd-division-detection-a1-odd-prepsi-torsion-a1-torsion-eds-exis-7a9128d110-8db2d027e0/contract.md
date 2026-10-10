<!-- theorem-id: fermat-p03/root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_sum_zero-a1 -->

## Theorem `Submission.p03_eds_torsion_kernel_sum_68cf3476_d4`

Let k be an algebraically closed field of characteristic zero with decidable equality, and let W be a Weierstrass curve over k with W.Δ ≠ 0. Let n > 0 be a natural number and S a finite set of points in W.toAffine.Point such that P belongs to S exactly when n • P = 0. Then the sum of the points of S, using the Weierstrass point-group addition, is zero.

Node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_sum_zero-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/367

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/407

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/433, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/434

## Lean problem

Declaration: `Submission.p03_eds_torsion_kernel_sum_68cf3476_d4`

```lean
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k), W.Δ ≠ 0 → ∀ n : ℕ, 0 < n → ∀ S : Finset W.toAffine.Point, (∀ P : W.toAffine.Point, P ∈ S ↔ n • P = 0) → S.sum (fun P => P) = 0
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


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/808

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
