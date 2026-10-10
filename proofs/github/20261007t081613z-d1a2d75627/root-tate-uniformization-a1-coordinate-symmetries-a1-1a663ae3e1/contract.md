<!-- theorem-id: fermat-p03/root.tate_uniformization-a1.coordinate_symmetries-a1 -->

## Theorem `Submission.p03_tu_coordinate_symmetries_68cf3476`

Let F be a complete normed field and Ω an algebraic normed extension with a NormedAlgebra F Ω structure. Assume Ω has an ultrametric norm. Let q ∈ F satisfy 0 < ‖q‖ < 1, let c ∈ F, and put Q = algebraMap F Ω q and C = algebraMap F Ω c. Define X(u) = Σ_{n∈ℤ} Q^n u/(1−Q^n u)^2−2C and Y(u) = Σ_{n∈ℤ}(Q^n u)^2/(1−Q^n u)^3+C. For every u ∈ Ωˣ outside Q^ℤ, one has X(Qu)=X(u), Y(Qu)=Y(u), X(u⁻¹)=X(u), and Y(u⁻¹)=−Y(u)−X(u). For every F-algebra automorphism σ of Ω one also has X(σu)=σ(X(u)) and Y(σu)=σ(Y(u)).

Node: `root.tate_uniformization-a1.coordinate_symmetries-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/332

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/355, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/356

Decomposition children: None

## Lean problem

Declaration: `Submission.p03_tu_coordinate_symmetries_68cf3476`

```lean
∀ (F Ω : Type) [NormedField F] [CompleteSpace F] [NormedField Ω] [NormedAlgebra F Ω] [Algebra.IsAlgebraic F Ω], (∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 → ∀ c : F, let qΩ : Ω := algebraMap F Ω q; let X : Ω → Ω := fun u => (∑' n : ℤ, qΩ ^ n * u / (1 - qΩ ^ n * u) ^ 2) - 2 * algebraMap F Ω c; let Y : Ω → Ω := fun u => (∑' n : ℤ, (qΩ ^ n * u) ^ 2 / (1 - qΩ ^ n * u) ^ 3) + algebraMap F Ω c; ∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → X (qΩ * (u : Ω)) = X (u : Ω) ∧ Y (qΩ * (u : Ω)) = Y (u : Ω) ∧ X ((u : Ω)⁻¹) = X (u : Ω) ∧ Y ((u : Ω)⁻¹) = -Y (u : Ω) - X (u : Ω) ∧ ∀ σ : Ω ≃ₐ[F] Ω, X (σ (u : Ω)) = σ (X (u : Ω)) ∧ Y (σ (u : Ω)) = σ (Y (u : Ω))
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
- Child DAG node: `root.tate_uniformization-a1.coordinate_symmetries-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write A(z) = z/(1−z)^2 and B(z) = z^2/(1−z)^3, and retain Q and C from the statement. Norm preservation of the algebra map gives Q ≠ 0. Fix a unit u outside Q^ℤ. Every Q^n u is nonzero and differs from one, since Q^n u = 1 would give u = Q^(−n).

2. The nonzero elements Qu and u⁻¹ also lie outside Q^ℤ: equations Qu = Q^m and u⁻¹ = Q^m would respectively imply u = Q^(m−1) and u = Q^(−m). An F-algebra automorphism σ fixes Q and C. If σ(u) = Q^m, applying σ⁻¹ gives u = Q^m, so σ(u) is likewise outside Q^ℤ. Regard these nonzero elements as units. The sibling bilateral_summability theorem applies with the given F, Ω and q to each of them. Therefore all A- and B-families used below are summable in Ω, and their sums may be reindexed and added.

3. For every integer n, Q^n(Qu) = Q^(n+1)u. Translation n ↦ n+1 is a bijection of ℤ, so reindexing gives Σ_n A(Q^n Qu) = Σ_n A(Q^n u) and the analogous equality for B. Subtracting 2C and adding C respectively proves X(Qu)=X(u) and Y(Qu)=Y(u).

4. For nonzero z ≠ 1, the identity 1−z⁻¹ = −(1−z)/z gives A(z⁻¹)=A(z). It also gives B(z⁻¹)=−z/(1−z)^3=−B(z)−A(z). Reindex the series at u⁻¹ by n ↦ −n and use Q^(−n)u⁻¹=(Q^n u)⁻¹. Thus its A-sum equals the A-sum at u, and its B-sum equals minus the B-sum at u minus the A-sum at u. If these latter sums are S_A and S_B, then X(u⁻¹)=S_A−2C=X(u), while Y(u⁻¹)=−S_B−S_A+C=−(S_B+C)−(S_A−2C)=−Y(u)−X(u).

5. Fix an F-algebra automorphism σ. The sibling algebraic_aut_isometry theorem applies with the given complete base, algebraic extension and q, so σ is an isometry and hence continuous. It preserves addition, multiplication, inverses and integer powers, and fixes Q. Consequently σ(A(Q^n u))=A(Q^n σ(u)) and σ(B(Q^n u))=B(Q^n σ(u)) for every n.

6. Apply σ to the convergent nets of finite partial sums of the two series at u. Continuity and step 5 show that their limits are the corresponding sums at σ(u); uniqueness of limits in the normed field Ω identifies these limits. Since σ fixes C and the integer 2, subtracting 2C and adding C gives X(σ(u))=σ(X(u)) and Y(σ(u))=σ(Y(u)). Together with steps 3 and 4, these are all the claimed identities.

## Key steps

1. Check that translation, inversion and algebraic automorphisms preserve the nonkernel domain.
2. Apply bilateral summability to justify all sum manipulations.
3. Reindex by integer translation to prove periodicity.
4. Reindex by negation and use two rational identities to prove inversion formulas.
5. Apply automorphism isometry to obtain continuity.
6. Pass automorphisms through convergent sums and fixed base-field constants.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/574

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
