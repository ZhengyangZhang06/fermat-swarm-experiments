<!-- theorem-id: fermat-p03/root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.eds_recurrence_uniqueness-a1 -->

## Theorem `Submission.p03_eds_recurrence_unique_68cf3476_d3`

Let R be a commutative integral domain and h∈R with h≠0. Let f,g:ℕ→R agree at every n≤4. Suppose each sequence s=f and s=g satisfies s(2r+1)=s(r+2)s(r)³−s(r−1)s(r+1)³ for every r≥2, and hs(2r)=s(r)(s(r+2)s(r−1)²−s(r−2)s(r+1)²) for every r≥3. Then f(n)=g(n) for every n∈ℕ.

Node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.eds_recurrence_uniqueness-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/368

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p03_eds_recurrence_unique_68cf3476_d3`

```lean
∀ (R : Type) [CommRing R] [IsDomain R] (h : R), h ≠ 0 → ∀ f g : ℕ → R, (∀ n : ℕ, n ≤ 4 → f n = g n) → (∀ r : ℕ, 2 ≤ r → f (2 * r + 1) = f (r + 2) * f r ^ 3 - f (r - 1) * f (r + 1) ^ 3) → (∀ r : ℕ, 3 ≤ r → h * f (2 * r) = f r * (f (r + 2) * f (r - 1) ^ 2 - f (r - 2) * f (r + 1) ^ 2)) → (∀ r : ℕ, 2 ≤ r → g (2 * r + 1) = g (r + 2) * g r ^ 3 - g (r - 1) * g (r + 1) ^ 3) → (∀ r : ℕ, 3 ≤ r → h * g (2 * r) = g r * (g (r + 2) * g (r - 1) ^ 2 - g (r - 2) * g (r + 1) ^ 2)) → ∀ n : ℕ, f n = g n
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

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_identification-a1.eds_recurrence_uniqueness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix R,h,f,g and all the stated hypotheses. Prove f(n)=g(n) by strong induction on n. At the induction step, assume f(j)=g(j) for every natural j<n.
2. If n≤4, the asserted equality is exactly the initial-agreement hypothesis. Otherwise n≥5.
3. Suppose n is odd. Write n=2r+1. The bound n≥5 implies r≥2. Since r+2<2r+1, all four indices r−1,r,r+1,r+2 are less than n. The induction hypothesis therefore identifies f and g at every index appearing on the right side of the odd recurrence. Apply that recurrence first to f, substitute these four equalities, and apply the recurrence for g in reverse. This gives f(n)=f(r+2)f(r)³−f(r−1)f(r+1)³=g(r+2)g(r)³−g(r−1)g(r+1)³=g(n).
4. Suppose n is even. Write n=2r. Since n≥5 and n is even, r≥3. The inequality r+2<2r shows that every index r−2,r−1,r,r+1,r+2 is less than n. Substituting the induction equalities into the two even recurrences gives h f(n)=f(r)(f(r+2)f(r−1)²−f(r−2)f(r+1)²)=g(r)(g(r+2)g(r−1)²−g(r−2)g(r+1)²)=h g(n). Thus h(f(n)−g(n))=0. Because R has no zero divisors and h≠0, f(n)−g(n)=0, hence f(n)=g(n).
5. Every natural n is covered by the base case or one of the two parity cases. Strong induction proves f(n)=g(n) for all n.

## Key steps

1. Use strong induction on the sequence index.
2. Discharge indices 0 through 4 using initial agreement.
3. For n=2r+1≥5, all recurrence indices are smaller; substitute induction equalities into the odd recurrence.
4. For n=2r≥6, all recurrence indices are smaller; the even recurrences give h f(n)=h g(n).
5. Cancel the nonzero factor h in the integral domain and conclude the induction.

## Reference use

### local-project

Queries:
- `preΨ.|ψ₂|Ψ₂Sq`
- `namespace CoordinateRing|def basis|lemma.*basis|instance.*IsDomain|noncomputable.*basis|mk.*ne_zero|repr`
- `uniqu|ext|eq_of`
- `python3 /tmp/p03-eds-decomposition-check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
- `/tmp/p03-eds-decomposition-ubcfsypt/TypesAfterSubmission.lean.log`
- `/tmp/p03-eds-decomposition-ubcfsypt/result.json`

The pinned project revision is 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib revision is db584cd6d46c92f209a44c0f1c829460d327499d. DivisionPolynomial/Basic.lean supplies preΨ'_zero through preΨ'_four, preΨ'_even, preΨ'_odd, and CoordinateRing.mk_ψ₂_sq. Affine/Point.lean supplies the basis {1,Y}, smul_basis_eq_zero, and the coordinate-ring domain instance without a discriminant hypothesis; Affine/Basic.lean gives polynomialY with Y coefficient 2. No matching arbitrary-sequence uniqueness theorem was found in EllipticDivisibilitySequence.lean. Both proposed types elaborated after literal import Submission using the node's frozen proof-base context and the authorized disposable header copy. Lean confirmed the AdjoinRoot commutative-ring instance and CoordinateRing.instIsDomain; inspected library dependencies use only propext, Classical.choice, and Quot.sound. Pinned trees were clean before and after checking, and neither proposed name appeared in the ten inspected DAG registries. The diagnostic receipt records the required policy digest, exact omitted lines 10–11, reversible original/build hashes, and a successful absence probe for all 37 omitted targets. These are interface diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/571

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
