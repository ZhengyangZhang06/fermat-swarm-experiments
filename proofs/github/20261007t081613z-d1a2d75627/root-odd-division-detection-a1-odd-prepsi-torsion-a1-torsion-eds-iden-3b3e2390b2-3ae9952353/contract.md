<!-- theorem-id: fermat-p03/root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1 -->

## Theorem `Submission.p03_torsion_eds_identification_68cf3476_d2`

Let k be a characteristic-zero field with decidable equality and W any Weierstrass equation over k. Let A=k[X,Y]/(W(X,Y)), let q:k[X,Y]→A be the quotient map, and put h=q(W.ψ₂). Suppose f:ℕ→A satisfies f₀=0, f₁=1, f₂=h, f₃=q(C(W.Ψ₃)), f₄=h q(C(W.preΨ₄)); f_(2r+1)=f_(r+2)f_r³−f_(r−1)f_(r+1)³ for every r≥2; and h f_(2r)=f_r(f_(r+2)f_(r−1)²−f_(r−2)f_(r+1)²) for every r≥3. Then for every n∈ℕ, f_n=q(C(W.preΨ' n))·h if n is even and f_n=q(C(W.preΨ' n)) if n is odd. Here C is the inclusion k[X]→k[X,Y]. No discriminant or algebraic-closedness hypothesis is imposed.

Node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/344

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/391, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/392

## Lean problem

Declaration: `Submission.p03_torsion_eds_identification_68cf3476_d2`

```lean
∀ (k : Type) [Field k] [CharZero k] [DecidableEq k] (W : WeierstrassCurve k), let q := WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine; let h := q W.ψ₂; ∀ f : ℕ → W.toAffine.CoordinateRing, (f 0 = 0 ∧ f 1 = 1 ∧ f 2 = h ∧ f 3 = q (Polynomial.C W.Ψ₃) ∧ f 4 = h * q (Polynomial.C W.preΨ₄) ∧ (∀ r : ℕ, 2 ≤ r → f (2 * r + 1) = f (r + 2) * f r ^ 3 - f (r - 1) * f (r + 1) ^ 3) ∧ (∀ r : ℕ, 3 ≤ r → h * f (2 * r) = f r * (f (r + 2) * f (r - 1) ^ 2 - f (r - 2) * f (r + 1) ^ 2))) → ∀ n : ℕ, f n = q (Polynomial.C (W.preΨ' n)) * (if Even n then h else 1)
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

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, W, q, h, and f satisfying the hypotheses, and put A=W.toAffine.CoordinateRing and a_n=q(Polynomial.C (W.preΨ' n)). The ring A is an integral domain, as supplied by the pinned coordinate-ring construction over a field. As a k[X]-module it is free with basis 1,y, where y=q(Polynomial.X). The element h equals (a₁X+a₃)·1+2y in this basis. Its y coefficient is 2≠0 in characteristic zero, so h≠0. Cancellation of h in A is consequently valid, regardless of whether W has nonzero discriminant.
2. Set g=q(Polynomial.C W.Ψ₂Sq). The pinned identity ψ₂²=C(Ψ₂Sq)+4W(X,Y) gives h²=g after applying q, since q kills the defining equation. Hence h⁴=g². Applying q∘Polynomial.C to the pinned initial values gives a₀=0, a₁=a₂=1, a₃=q(Polynomial.C W.Ψ₃), and a₄=q(Polynomial.C W.preΨ₄). Here indexed a_n denotes the sequence just defined, not a Weierstrass coefficient.
3. Applying the same ring homomorphism to the pinned even recurrence and reindexing yields a_(2r)=a_r(a_(r+2)a_(r−1)²−a_(r−2)a_(r+1)²) for r≥3. The pinned odd recurrence gives a_(2r+1)=g²a_(r+2)a_r³−a_(r−1)a_(r+1)³ for even r≥2, and a_(2r+1)=a_(r+2)a_r³−g²a_(r−1)a_(r+1)³ for odd r≥2. Its original index is r−2, which has the same parity as r; the even recurrence's original index is r−3. Thus these formulas apply for exactly the stated bounds.
4. Prove f_n=a_n times h for even n and f_n=a_n for odd n by strong induction on n. At n=0 both sides are zero. At n=1,2,3,4 the assumed initial values and step 2 give the result, using commutativity for n=4.
5. Suppose n≥5 is odd. Write n=2r+1 with r≥2. The indices r−1,r,r+1,r+2 are all less than n, since r+2<2r+1 for r≥2. If r is even, substitution of the induction hypotheses into f_(2r+1)=f_(r+2)f_r³−f_(r−1)f_(r+1)³ gives h⁴a_(r+2)a_r³−a_(r−1)a_(r+1)³. If r is odd, it gives a_(r+2)a_r³−h⁴a_(r−1)a_(r+1)³. By h⁴=g² and step 3, each is a_(2r+1). This is the claimed formula for odd n.
6. Suppose n≥5 is even. Then n=2r with r≥3. All indices r−2,r−1,r,r+1,r+2 are nonnegative and less than 2r, the largest inequality being r+2<2r for r≥3. If r is even, f_r and f_(r±2) each contribute one factor h, while f_(r±1) contribute none. If r is odd, those first three factors contribute none and each squared f_(r±1) contributes h². In either case the right side of the assumed even recurrence equals h²a_r(a_(r+2)a_(r−1)²−a_(r−2)a_(r+1)²)=h²a_(2r). Hence h f_(2r)=h²a_(2r). Cancel h using step 1 to obtain f_(2r)=h a_(2r)=a_(2r)h. This is the claimed formula for even n.
7. Every n≥5 is covered by steps 5 and 6, so strong induction proves the asserted identity for every natural n. The argument used only the supplied initial values and recurrences and pinned ring identities, and required neither algebraic closedness nor nonsingularity.

## Key steps

1. Use the free basis 1,Y to show h≠0 in the integral coordinate ring.
2. Map the pinned identity ψ₂²=C(Ψ₂Sq)+4W and the initial preΨ' values into the coordinate ring.
3. Reindex the pinned even and odd preΨ' recurrences.
4. Verify indices 0 through 4.
5. Perform the odd induction step, replacing the four factors h by (q(C(Ψ₂Sq)))².
6. Perform the even induction step and cancel the nonzero factor h.
7. Conclude the parity-adjusted formula for every natural index.

## Reference use

### local-project

Queries:
- `map_preΨ|preΨ.*eval|eval.*preΨ|FunctionField|divisor|torsion`
- `preΨ.*(torsion|nsmul|smul.*zero)|(?:torsion|nsmul).*preΨ|torsion_eds|eds_identification`
- `unique|ext|rec|strong|eq_norm|eq_preNorm`
- `rg -n 'p03_torsion_eds_exists_68cf3476_d2|p03_torsion_eds_identification_68cf3476_d2' --hidden --glob '*.lean' --glob 'dag.json' /mnt/data/zhengyang-workspace/fermat-swarm-projects`
- `python3 /tmp/p03_torsion_split_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-odd-division-detection-a1-odd-prepsi-torsion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p03-torsion-split-7jddr0do/TypesAfterSubmission.lean`
- `/tmp/p03-torsion-split-7jddr0do/TypesAfterSubmission.lean.log`
- `/tmp/p03-torsion-split-7jddr0do/InstancesAndAxioms.lean.log`
- `/tmp/p03-torsion-split-7jddr0do/DomainAxioms.lean.log`
- `/tmp/p03-torsion-split-7jddr0do/TargetAbsence.lean`
- `/tmp/p03-torsion-split-7jddr0do/results.json`

The frozen handoff identifies this as the torsion-detection node at depth 2. Basic.lean provides the exact initial polynomials, preΨ' recurrences, mk_ψ₂_sq, and map_preΨ'. Point.lean provides the integral coordinate ring, its free basis, point ideals, quotient evaluation, and injective point base change. EllipticDivisibilitySequence.lean provides normEDSRec' for the required induction. Searches found no relevant theorem already proving the proposed torsion criterion or recurrence-identification contract. Both exact child types elaborate after import Submission in disposable compiler copies. Instance inspection confirms AdjoinRoot.instCommRing multiplication and WeierstrassCurve.Affine.Point.instAddCommGroup scalar multiplication. The type expressions and inspected library infrastructure transitively use only propext, Classical.choice, and Quot.sound. Ten DAGs and local Lean declarations were searched without name collisions. Snapshot revisions 81f093181fd6c58dc887fcae5ec8b896996f1885 and db584cd6d46c92f209a44c0f1c829460d327499d and pinned package revisions were clean and matching. Header diagnostics verified policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, the exact omissions at lines 10 and 11, original hash dd8891addb75e48583885c932518af8bc6d34438aec4e3ccd76ce6aa765e423f, derived hash 81502485ae6796527a5c4e210837b198322b438244a2f58054b94b98aef9dda9, reversible reconstruction, and Lean-checked absence of all 37 targets. Protected original files remained unchanged. These are interface diagnostics, not comparator acceptance of either proposed proof.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
