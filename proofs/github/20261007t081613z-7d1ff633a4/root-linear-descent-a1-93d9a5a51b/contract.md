<!-- theorem-id: fermat-p08/root.linear_descent-a1 -->

## Theorem `Submission.p08_7d1ff633a4_linear_descent`

Let k be a field and X, Y, X′, Y′ arbitrary k-vector spaces. Let n ∈ k be nonzero. Suppose linear maps R_X : X → X′, C_X : X′ → X, R_Y : Y → Y′, C_Y : Y′ → Y satisfy C_X(R_Xx) = n·x and C_Y(R_Yy) = n·y. Let Θ : X →ₗ[k] Y* and Θ′ : X′ →ₗ[k] (Y′)* satisfy Θ′(R_Xx)(y′) = Θ(x)(C_Yy′) and Θ′(x′)(R_Yy) = Θ(C_Xx′)(y) for all arguments. If Θ′ is bijective, then Θ is bijective. The duals are full algebraic duals, and no finite-dimensionality assumption is made.

Node: `root.linear_descent-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_linear_descent`

```lean
∀ {k X Y X' Y' : Type} [Field k] [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] [AddCommGroup X'] [Module k X'] [AddCommGroup Y'] [Module k Y'] (n : k) (hn : n ≠ 0) (R_X : X →ₗ[k] X') (C_X : X' →ₗ[k] X) (R_Y : Y →ₗ[k] Y') (C_Y : Y' →ₗ[k] Y) (Θ : X →ₗ[k] Module.Dual k Y) (Θ' : X' →ₗ[k] Module.Dual k Y'), (∀ x : X, C_X (R_X x) = n • x) → (∀ y : Y, C_Y (R_Y y) = n • y) → (∀ (x : X) (y' : Y'), Θ' (R_X x) y' = Θ x (C_Y y')) → (∀ (x' : X') (y : Y), Θ' x' (R_Y y) = Θ (C_X x') y) → Function.Bijective Θ' → Function.Bijective Θ
```

### Frozen project context

`Fermat/Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.lean` at `9db4b2bea94e42612c675170cfe30ec626166658` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q)) (U : Subgroup S) [U.FiniteIndex] (hUp : IsUnit ((U.index : ℕ) : ZMod p))
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ U)
    (hTU : FiniteDimensional (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) ∧
      finrank (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) = 1)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (hres : ∀ (invU : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) →ₗ[ZMod p] ZMod p),
      Function.Bijective invU →
      ∀ (θ₀ : (Rep.res U.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta0 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₀ →
      ∀ (θ₁ : continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₁ →
      ∀ (θ₂ : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))).ρ.invariants),
        IsTheta2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₀)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₁)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.linear_descent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Suppose Θ(x) = 0. For every y′ ∈ Y′, the first compatibility gives Θ′(R_Xx)(y′) = Θ(x)(C_Yy′) = 0. Extensionality of linear functionals gives Θ′(R_Xx) = 0 = Θ′(0). Injectivity of Θ′ therefore gives R_Xx = 0.
2. Apply C_X. The composite identity yields n·x = 0. Multiplying by n⁻¹ gives x = 0 because n ≠ 0. If Θ(x₁) = Θ(x₂), linearity gives Θ(x₁−x₂) = 0, so the preceding argument implies x₁ = x₂. Thus Θ is injective.
3. Let λ ∈ Y* be arbitrary. The composite λ ∘ C_Y is a linear functional on Y′. By surjectivity of Θ′ choose x′ ∈ X′ with Θ′(x′) = λ ∘ C_Y. Define x = n⁻¹·C_Xx′.
4. For every y ∈ Y, linearity, the second compatibility, and the composite identity for Y give Θ(x)(y) = n⁻¹Θ(C_Xx′)(y) = n⁻¹Θ′(x′)(R_Yy) = n⁻¹λ(C_Y(R_Yy)) = n⁻¹λ(n·y) = λ(y). The final equality uses linearity of λ and n⁻¹n = 1. Extensionality gives Θ(x) = λ.
5. Since λ was arbitrary, Θ is surjective. Combined with Step 2, this proves bijectivity without any dimension assumption.

## Key steps

1. Use the first compatibility and injectivity of Θ′ to show ker Θ maps into ker R_X.
2. Cancel n in C_XR_X = n id to prove injectivity.
3. Lift λ ∘ C_Y through Θ′.
4. Normalize the transferred lift by n⁻¹.
5. Use the second compatibility and C_YR_Y = n id to prove surjectivity.

## Reference use

### local-project

Queries:
- `rg -n 'normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup|corestriction|projection_formula|IsTheta.*exists|exists.*IsTheta|p08_7d1ff633a4_' project/Definitions mathlib/Mathlib`
- `rg -n 'normalClosure|finiteDimensional|instModule|of_coe' mathlib/Mathlib/FieldTheory/Normal/Closure.lean mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean`
- `rg -n 'normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup|IsTheta.*exists|exists.*IsTheta|p08_7d1ff633a4_' project/Definitions mathlib/Mathlib`
- `sed -n '195,240p' mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `sed -n '960,995p' mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `git rev-parse HEAD`
- `git status --porcelain`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -j1 Combined.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2Map.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousDuality.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_Selmer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_DualSelmer_ExtConditions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_ExtCitation_KummerBridge.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_ExtCitation_AdmissibleExtension.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/Normal/Closure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/decomposition-type-check-20261008/Combined.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/decomposition-type-check-20261008/Combined.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/decomposition-type-check-20261008/combined-result.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/decomposition-type-check-20261008/provenance.json`

Project revision 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d match the manifest and have clean trees; installed dependencies also match clean pins. ContinuousH1 is an image of level cocycles in ordinary H1; continuousH2 is the quotient by boundaries from level one-cochains. Inspected the precise theta predicates, cup formula, restriction carriers, twisted-dual action, cyclotomic specification and uniqueness, normal-closure instances, and ModuleCat.of. The targeted search found no existing proposed names, fixing-subgroup instances, or theta-existence theorem. Broad corestriction matches concern ordinary homology or unrelated range restrictions, not the required continuous transfer/theta package. Fresh literal-import checks in the existing matching policy-derived Submission context passed for all five unchanged expressions, all 24 indexed additive/module instance equalities, and the global/restricted evaluation pairing coercions. Inspected type and library transitive axioms are confined to propext, Classical.choice, and Quot.sound. A separate fresh context rebuild timed out. These diagnostics do not accept any theorem proof, and no upstream target solution was imported.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/387

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
