<!-- theorem-id: fermat-p03/root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_sum_zero-a1.negation_fixed_sum-a1 -->

## Theorem `Submission.p03_eds_negation_fixed_sum_68cf3476_d5`

Let G be an additive commutative group with decidable equality. Let S be a finite subset of G such that −x belongs to S whenever x belongs to S. Then the sum of all elements of S equals the sum of those elements x of S satisfying 2 • x = 0, where scalar multiplication is natural-number repeated addition.

Node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_sum_zero-a1.negation_fixed_sum-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/408

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p03_eds_negation_fixed_sum_68cf3476_d5`

```lean
∀ (G : Type) [AddCommGroup G] [DecidableEq G] (S : Finset G), (∀ x ∈ S, -x ∈ S) → S.sum (fun x => x) = (S.filter (fun x => (2 : ℕ) • x = 0)).sum (fun x => x)
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

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_sum_zero-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_sum_zero-a1.negation_fixed_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix G as in the statement. For any finite subset A of G, write F(A) = {x ∈ A : 2 • x = 0}. Since 2 • x = x + x, the equation 2 • x = 0 is equivalent to x = −x: each says that x is its own additive inverse.
2. Prove the asserted equality for every negation-stable S by strong induction on its cardinality. If every element of S is killed by 2, then F(S) = S and the equality is immediate. This includes the empty-set case.
3. Otherwise choose a ∈ S with 2 • a ≠ 0. Negation stability gives −a ∈ S, and step 1 gives a ≠ −a. Moreover 2 • (−a) = −(2 • a) ≠ 0. Define R = S \ {a, −a}. It is a proper subset of S, since a belongs to S and does not belong to R, so its cardinality is strictly smaller.
4. The set R is stable under negation. Indeed, if x ∈ R, then −x ∈ S. If −x = a, negating gives x = −a, contradicting x ∈ R. If −x = −a, negating gives x = a, again a contradiction. Thus −x lies in neither removed singleton and belongs to R.
5. Neither removed element is killed by 2, so F(R) = F(S). More explicitly, an element of F(R) lies in S and is killed by 2, hence lies in F(S). Conversely, an element of F(S) cannot equal either a or −a by step 3, so it belongs to R and therefore to F(R).
6. The set S is the disjoint union of R and the two-element set {a, −a}. Hence its sum is the sum of R plus a + (−a), which equals the sum of R. The induction hypothesis applies to R by steps 3–4 and identifies its sum with the sum of F(R). Step 5 identifies this with the sum of F(S), proving the required equality and completing the induction.

## Key steps

1. Identify points killed by 2 with fixed points of negation.
2. Use strong induction on the cardinality of the negation-stable finite set.
3. Remove a distinct pair a and −a when a is not fixed.
4. Prove that the remainder stays negation-stable and has the same two-torsion subset.
5. Cancel the removed pair and apply the induction hypothesis.

## Reference use

### local-project

Queries:
- `sum_involution|sum.*eq.*neg|sum.*filter.*(neg|two)|sum.*(torsion|orderOf)|sum.*eq_zero`
- `instance.*(AddCommGroup|AddGroup)|nsmul :=|nsmulBinRec|deriving.*DecidableEq`
- `sum.*(torsion|card_four|card.*4|two_nsmul)|sum_eq_sum.*(filter|neg)|sum.*filter.*two`
- `prod.*(invol|eq_one|card)|card.*4|Klein`
- `p03_eds_negation_fixed_sum_68cf3476_d5|p03_eds_two_torsion_four_sum_68cf3476_d5`
- `python3 /tmp/p03_eds_sum_decomposition_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/GroupTheory/FiniteAbelian`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p03_eds_sum_split_ngfjxqfk/ChildTypes.lean`
- `/tmp/p03_eds_sum_split_ngfjxqfk/ChildTypes.lean.log`
- `/tmp/p03_eds_sum_split_ngfjxqfk/InstancesAxioms.lean.log`
- `/tmp/p03_eds_sum_split_ngfjxqfk/TargetAbsence.lean`
- `/tmp/p03_eds_sum_split_ngfjxqfk/receipt.json`

The snapshot and compiler dependencies matched their pinned revisions and were clean: project 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Finset/Basic.lean supplies Finset.sum_involution through to_additive; Affine/Point.lean supplies decidable equality and the canonical additive commutative point group. Targeted searches found no matching four-element two-torsion sum theorem in the searched modules. Both proposed exact types elaborated after import Submission in a disposable copy of proof base 3faf7ece669acd01820d0d4ce378f0b98a1944a6. Lean confirmed the point-group instance and definitionally checked its natural scalar multiplication against nsmulBinRec. The inspected library declarations use only propext, Classical.choice and Quot.sound, or no axioms. Neither proposed name occurs in the ten local problem DAGs or the imported environment. The matching header policy had digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; only lines 10 and 11 were omitted in the disposable compiler copy, and Lean checked all 37 targets absent. The receipt records exact omitted lines, original/build hashes and byte-exact reversibility. Repository files remained unchanged. These are interface diagnostics, not comparator acceptance of child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/588

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
