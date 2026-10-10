<!-- theorem-id: fermat-p03/root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.two_torsion_card-a1 -->

## Theorem `Submission.p03_tkc_two_torsion_card_68cf3476_d5`

Let k be an algebraically closed field of characteristic zero with decidable equality, and let W be a Weierstrass curve over k with W.Δ ≠ 0. Then Nat.card {P : W.toAffine.Point // (2 : ℕ) • P = 0} = 4, including the identity among these four points.

Node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1.two_torsion_card-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/407

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p03_tkc_two_torsion_card_68cf3476_d5`

```lean
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k), W.Δ ≠ 0 → Nat.card {P : W.toAffine.Point // (2 : ℕ) • P = 0} = 4
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


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/592

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
