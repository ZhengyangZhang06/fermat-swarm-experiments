<!-- theorem-id: fermat-p03/root.odd_division_detection-a1.odd_prepsi_degree_lc-a1 -->

## Theorem `Submission.p03_odd_prepsi_degree_lc_68cf3476`

Let F be a characteristic-zero field with decidable equality, W a Weierstrass equation over F, and n an odd natural number with 3 ≤ n. Then (W.preΨ' n).natDegree = (n² − 1)/2 and (W.preΨ' n).leadingCoeff = n, with n interpreted in F in the second equality. No discriminant hypothesis is required.

Node: `root.odd_division_detection-a1.odd_prepsi_degree_lc-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/331

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p03_odd_prepsi_degree_lc_68cf3476`

```lean
∀ (F : Type) [Field F] [CharZero F] [DecidableEq F] (W : WeierstrassCurve F) (n : ℕ), 3 ≤ n → Odd n → (W.preΨ' n).natDegree = (n ^ 2 - 1) / 2 ∧ (W.preΨ' n).leadingCoeff = (n : F)
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

- Parent DAG node: `root.odd_division_detection-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_degree_lc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix F, W and n satisfying the hypotheses. Since 3 ≤ n, n is nonzero. Characteristic zero makes the natural-number map into F injective, so (n : F) ≠ 0.
2. The pinned theorem WeierstrassCurve.natDegree_preΨ' applies to any Weierstrass equation over a commutative ring whenever (n : R) ≠ 0. Applied here, it gives (W.preΨ' n).natDegree = (n² − (if Even n then 4 else 1))/2. Its hypotheses hold because F is a field and step 1 supplies the required nonzero cast.
3. An odd natural number is not even. Consequently the conditional in step 2 selects 1, giving (W.preΨ' n).natDegree = (n² − 1)/2.
4. The pinned theorem WeierstrassCurve.leadingCoeff_preΨ', with the same nonzero-cast hypothesis, gives the leading coefficient as the natural-number cast of n/2 when n is even and the cast of n otherwise. Since n is odd, the latter case applies and (W.preΨ' n).leadingCoeff = (n : F).
5. Combining steps 3 and 4 proves the asserted conjunction. Both invoked results concern the exact preΨ' sequence in the frozen Basic.lean definition; their pinned proofs are in DivisionPolynomial/Degree.lean and do not assume a nonzero discriminant.

## Key steps

1. Use 3 ≤ n and characteristic zero to show (n : F) ≠ 0.
2. Apply the pinned exact natDegree_preΨ' formula.
3. Use oddness to eliminate the even branch.
4. Apply leadingCoeff_preΨ' and combine the two equalities.

## Reference use

### local-project

Queries:
- `rg -n 'preΨ.*(degree|natDegree|leadingCoeff)|[[:alnum:]_]*(degree|natDegree|leadingCoeff).*preΨ|preΨ.*(smul|torsion)|map_preΨ' .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481`
- `rg -n 'preΨ.*(torsion|nsmul|smul.*zero)|(?:torsion|nsmul).*preΨ' .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions`
- `rg -n 'p03_odd_prepsi_degree_lc_68cf3476|p03_odd_prepsi_torsion_68cf3476' --hidden --glob '*.lean' --glob 'dag.json' /mnt/data/zhengyang-workspace/fermat-swarm-projects`
- `python3 /tmp/p03_odd_split_probe.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p03-odd-split-vk58ilpb/results.json`
- `/tmp/p03-odd-split-vk58ilpb/TypesAfterSubmission.lean`
- `/tmp/p03-odd-split-vk58ilpb/TypesAfterSubmission.lean.log`
- `/tmp/p03-odd-split-vk58ilpb/InstancesAfterSubmission.lean.log`
- `/tmp/p03-odd-split-vk58ilpb/LibraryAxioms.lean.log`
- `/tmp/p03-odd-split-vk58ilpb/TargetAbsence.lean`

Basic.lean supplies the exact initial values, even and odd recurrences, and map_preΨ'. Degree.lean supplies natDegree_preΨ' and leadingCoeff_preΨ' under the hypothesis that the natural-number cast is nonzero. Affine/Point.lean supplies the intended additive group and injective coordinatewise base-change homomorphism. The torsion search found no relevant matching theorem; the identifier search and DAG inspection found no collisions. Fresh diagnostics confirmed clean project revision 81f093181fd6c58dc887fcae5ec8b896996f1885, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and matching pinned dependencies. Both exact child types elaborate after import Submission in a disposable compiler copy. Instance inspection confirms that natural scalar multiplication uses WeierstrassCurve.Affine.Point.instAddCommGroup. The type definitions and inspected library declarations transitively use only propext, Classical.choice, and Quot.sound. The recorded header repair verifies policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, exact omitted lines 10 and 11, original hash dd8891addb75e48583885c932518af8bc6d34438aec4e3ccd76ce6aa765e423f, derived hash 81502485ae6796527a5c4e210837b198322b438244a2f58054b94b98aef9dda9, reversible reconstruction, and successful Lean absence checks for all 37 targets. Original files remain unchanged. These checks establish interface compatibility, not comparator acceptance of either proposed theorem.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/379

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
