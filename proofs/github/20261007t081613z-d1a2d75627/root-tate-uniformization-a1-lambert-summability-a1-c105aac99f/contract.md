<!-- theorem-id: fermat-p03/root.tate_uniformization-a1.lambert_summability-a1 -->

## Theorem `Submission.p03_tu_lambert_summable_68cf3476`

Let F be a complete normed field satisfying ‖x+y‖ ≤ max(‖x‖,‖y‖) for all x,y ∈ F. If q ∈ F satisfies ‖q‖ < 1, then for every natural number k the family indexed by d ∈ ℕ with term ((d+1 : F)^k q^(d+1))/(1−q^(d+1)) is summable in F.

Node: `root.tate_uniformization-a1.lambert_summability-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/332

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p03_tu_lambert_summable_68cf3476`

```lean
∀ (F : Type) [NormedField F] [CompleteSpace F], (∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → ∀ q : F, ‖q‖ < 1 → ∀ k : ℕ, Summable (fun d : ℕ => ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1)))
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

- Parent DAG node: `root.tate_uniformization-a1`
- Child DAG node: `root.tate_uniformization-a1.lambert_summability-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write R = ‖q‖, so 0 ≤ R < 1. Induction on the natural number m gives ‖(m : F)‖ ≤ 1: the zero case is immediate, and the successor case follows from the ultrametric inequality applied to (m : F)+1. Consequently ‖(m : F)^k‖ ≤ 1 for every k, including k = 0.

2. If z ∈ F has ‖z‖ < 1, the ultrametric inequality gives ‖1−z‖ ≤ 1. This norm cannot be less than 1, because 1 = (1−z)+z would then have norm strictly less than 1. Thus ‖1−z‖ = 1. Apply this to z = q^(d+1), whose norm is R^(d+1) < 1.

3. Multiplicativity of the field norm and step 2 give ‖((d+1 : F)^k q^(d+1))/(1−q^(d+1))‖ ≤ R^(d+1) for every d.

4. The real geometric series with terms R^(d+1) is summable because 0 ≤ R < 1. The comparison theorem for series in a complete normed additive group, namely Summable.of_norm_bounded in the pinned library, applies to the estimate in step 3. It proves the required unordered summability in F for each k. This also covers q = 0, when every term is zero.

## Key steps

1. Bound the norm of every natural-number cast and its powers by one.
2. Show that ‖1−q^(d+1)‖ = 1.
3. Bound each Lambert summand by the real geometric term ‖q‖^(d+1).
4. Apply geometric summability and completeness-based norm comparison.

## Reference use

### local-project

Queries:
- `TateCurve|tateCurve|tateUniformization|LaurentAnalytic|Laurent.*annulus|lambert|Lambert`
- `FiniteDimensional.complete|LinearMap.continuous_of_finiteDimensional`
- `summable_of_norm_bounded|summable_geometric_of_norm_lt_one`
- `theorem Summable.of_norm_bounded|lemma Summable.of_norm_bounded|theorem Summable.of_norm|lemma Summable.of_norm`
- `exists_isWeierstrassFactorization|theorem complete|continuous_of_finiteDimensional|summable_norm_iff|multipliable.*norm|multipliable.*sub|tprod_ne_zero`
- `p03_tu_(lambert_summable|euler_product_powers|bilateral_summable|algebraic_aut_isometry|coordinate_symmetries)_68cf3476`
- `python3 /tmp/p03-tu-decomposition-14v63537/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Summable.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/NumberTheory/TsumDivisorsAntidiagonal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p03-tu-decomposition-14v63537/result.json`
- `/tmp/p03-tu-decomposition-14v63537/ExtraType.lean.log`
- `/tmp/p03-tu-decomposition-14v63537/LibraryEvidenceV2.lean.log`

The snapshot pins project 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. It supplies geometric-series comparison, finite-dimensional completeness and continuity, induced norms, infinite-product convergence infrastructure, and formal Weierstrass preparation. The Lambert-series search found divisor-sum identities, but no matching Tate uniformization or annular Laurent-analysis interface. All five proposed types elaborate after import Submission in a disposable compiler copy. The matching policy digest is 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; only lines 10 and 11 were omitted, after Lean confirmed all 37 targets absent. The reversible original/build hashes are dd8891addb75e48583885c932518af8bc6d34438aec4e3ccd76ce6aa765e423f and 81502485ae6796527a5c4e210837b198322b438244a2f58054b94b98aef9dda9. Pinned sources and dependencies were clean; the original sources were unchanged. Source searches and all ten local DAGs showed no proposed-name collisions. Induced intermediate-field norms and multiplication were checked. The five type expressions and seven inspected library theorems depend only on propext, Classical.choice and Quot.sound. These are interface diagnostics, not theorem-comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/380

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
