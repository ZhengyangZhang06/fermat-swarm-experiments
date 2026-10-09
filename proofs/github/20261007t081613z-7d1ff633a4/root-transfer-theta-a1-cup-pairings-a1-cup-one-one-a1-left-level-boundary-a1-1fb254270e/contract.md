<!-- theorem-id: fermat-p08/root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1.left_level_boundary-a1 -->

## Theorem `Submission.p08_7d1ff633a4_cp11_left_level_boundary`

Let k be a field, G a group, Ω=AlgebraicClosure ℚ, r:G→Autℚ(Ω) a group homomorphism, and A,B,N k-representations of G. Let φ:A→ₗ[k]B→ₗ[k]N be equivariant: φ(s·a,s·b)=s·φ(a,b) for all s,a,b. Fix a∈A and a one-cocycle g:G→B satisfying g(st)=s·g(t)+g(s). Assume g is level, meaning that some finite-dimensional rational intermediate field F⊆Ω satisfies g(th)=g(t) whenever r(h) fixes F. Define d₀a(s)=s·a−a. Then cupCochain φ (d₀a) g belongs to levelCoboundaries₂ r N, the image of the level one-cochains under d₁v(s,t)=s·v(t)−v(st)+v(s).

Node: `root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1.left_level_boundary-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/480

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_cp11_left_level_boundary`

```lean
∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (a : A) (g : groupCohomology.cocycles₁ B), groupCohomology.IsLevelConstant₁ r (⇑g) → groupCohomology.cupCochain φ (fun s : G => A.ρ s a - a) (⇑g) ∈ groupCohomology.levelCoboundaries₂ r N
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

- Parent DAG node: `root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1`
- Child DAG node: `root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1.left_level_boundary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data. Choose a finite-dimensional rational intermediate field F witnessing the level property of g, and define v:G→N by v(t)=φ(a,g(t)).
2. If r(h) fixes F, then v(th)=φ(a,g(th))=φ(a,g(t))=v(t). Thus the same F witnesses IsLevelConstant₁ r v, so v is a member of levelCochains₁ r N.
3. For arbitrary s,t∈G, equivariance gives s·φ(a,g(t))=φ(s·a,s·g(t)), and the one-cocycle identity gives g(st)=s·g(t)+g(s). Therefore d₁v(s,t)=φ(s·a,s·g(t))−φ(a,s·g(t)+g(s))+φ(a,g(s))=φ(s·a,s·g(t))−φ(a,s·g(t))=φ(s·a−a,s·g(t)), using linearity in the second argument to cancel φ(a,g(s)) and linearity in the first argument for the last equality.
4. The final expression is cupCochain φ (fun s↦s·a−a) g evaluated at (s,t). Equality at every pair gives equality of the two cochains. Since levelCoboundaries₂ r N is precisely the image of levelCochains₁ r N under (d₁₂ N).hom, the level cochain v is a preimage of the required cup cochain. This proves its membership in levelCoboundaries₂ r N.

## Key steps

1. Choose v(t)=φ(a,g(t)) as the boundary primitive.
2. Use the level field of g to prove that v is level.
3. Compute d₁v=cupCochain φ (d₀a) g using equivariance and the cocycle identity.
4. Use the defining image description of levelCoboundaries₂.

## Reference use

### local-project

Queries:
- `rg -n 'cupCochain|levelCocycles₁|levelCocycles₂|continuousH2π|H1π_eq_iff' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36 --glob '*.lean'`
- `rg -n 'finiteDimensional.*sup|finiteDimensional_sup|fixingSubgroup_antitone' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory`
- `rg -n 'continuous.*[Cc]up|[Cc]up.*continuous' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/Galois/Basic.lean`

The manifest pins project 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. CupProduct provides the ordinary bilinear cup and both boundary-primitive calculations. ContinuousH1 is an image of level one-cocycles; ContinuousH2 uses the image of level one-cochains as its boundary denominator. H1π_eq_iff, finiteDimensional_sup, and fixingSubgroup_antitone support descent and common level fields. The focused continuous-cup search found no matching theorem. The three project definition files match the snapshot byte-for-byte, and the local mathlib checkout is clean at the pinned commit. Diagnostic axiom checks of the three proposed types and cited declarations found only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
