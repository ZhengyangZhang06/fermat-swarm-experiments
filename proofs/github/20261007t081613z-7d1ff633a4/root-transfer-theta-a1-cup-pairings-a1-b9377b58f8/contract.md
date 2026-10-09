<!-- theorem-id: fermat-p08/root.transfer_theta-a1.cup_pairings-a1 -->

## Theorem `Submission.p08_7d1ff633a4_tt26_cup_pairings`

Let k be a field, G a group, Ω = AlgebraicClosure ℚ, r : G → Autℚ(Ω) a homomorphism, and A,B,N k-representations of G. Let E₀ ⊆ Ω be a finite-dimensional rational intermediate field such that r⁻¹(Fix(E₀)) acts trivially on B. Let φ : A →ₗ[k] B →ₗ[k] N satisfy φ(g·a,g·b)=g·φ(a,b). Write H⁰(V)=Vᴳ, H¹(V)=continuousH1 r V, and H²(V)=continuousH2 r V; set X_i=Hⁱ(A), Y_i=H²⁻ⁱ(B), for i=0,1,2. A level one-cocycle f has class [f] in the frozen continuousH1 image, and a level two-cocycle z has class [z] under continuousH2π. There exist bilinear maps P_i : X_i × Y_i → H²(N) with the following representative properties. For every invariant m and level two-cocycle z of B, there exists a level two-cocycle e of N with e(s,t)=φ(m,z(s,t)) and P₀(m,[z])=[e]. For every pair of level one-cocycles f of A and g of B, there exists a level two-cocycle e of N with e(s,t)=φ(f(s),s·g(t)) and P₁([f],[g])=[e]. For every level two-cocycle z of A and invariant d of B, there exists a level two-cocycle e of N with e(s,t)=φ(z(s,t),d) and P₂([z],d)=[e]. No normality or finite-index hypothesis is imposed here.

Node: `root.transfer_theta-a1.cup_pairings-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/349

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/479, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/480

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_tt26_cup_pairings`

```lean
∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E₀ → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ g b = b) → ∀ φ : A →ₗ[k] B →ₗ[k] N, (∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)) → let X : Fin 3 → ModuleCat k := ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 r A), ModuleCat.of k (groupCohomology.continuousH2 r A)]; let Y : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 r B), ModuleCat.of k (groupCohomology.continuousH1 r B), ModuleCat.of k B.ρ.invariants]; ∃ (P : ∀ i : Fin 3, X i →ₗ[k] Y i →ₗ[k] groupCohomology.continuousH2 r N), ((∀ (m : A.ρ.invariants) (z : groupCohomology.levelCocycles₂ r B), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ (m : A) ((z : G × G → B) st)) ∧ P 0 m (groupCohomology.continuousH2π r B z) = groupCohomology.continuousH2π r N e) ∧ (∀ (f : groupCohomology.cocycles₁ A) (hf : groupCohomology.IsLevelConstant₁ r (⇑f)) (g : groupCohomology.cocycles₁ B) (hg : groupCohomology.IsLevelConstant₁ r (⇑g)), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = groupCohomology.cupCochain φ (⇑f) (⇑g) st) ∧ P 1 ⟨(groupCohomology.H1π A).hom f, groupCohomology.H1π_mem_continuousH1 r A hf⟩ ⟨(groupCohomology.H1π B).hom g, groupCohomology.H1π_mem_continuousH1 r B hg⟩ = groupCohomology.continuousH2π r N e) ∧ (∀ (z : groupCohomology.levelCocycles₂ r A) (d : B.ρ.invariants), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ ((z : G × G → A) st) (d : B)) ∧ P 2 (groupCohomology.continuousH2π r A z) d = groupCohomology.continuousH2π r N e))
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

- Parent DAG node: `root.transfer_theta-a1`
- Child DAG node: `root.transfer_theta-a1.cup_pairings-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write d₀v(s)=s·v−v, d₁f(s,t)=s·f(t)−f(st)+f(s), and d₂z(s,t,u)=s·z(t,u)−z(st,u)+z(s,tu)−z(s,t), exactly the pinned differentials. Define the three proposed cocycle functions by e₀(s,t)=φ(m,z(s,t)), e₁(s,t)=φ(f(s),s·g(t)), and e₂(s,t)=φ(z(s,t),d).
2. If m is invariant, the linear map b↦φ(m,b) is equivariant, since s·φ(m,b)=φ(s·m,s·b)=φ(m,s·b). Therefore it commutes with d₁ and d₂, and e₀ is a two-cocycle. Likewise a↦φ(a,d) is equivariant when d is invariant, so e₂ is a two-cocycle. Their level conditions follow by postcomposition from the level condition of z.
3. For e₁, expand d₂e₁. Equivariance changes its first term into φ(s·f(t),st·g(u)). The one-cocycle identities f(st)=s·f(t)+f(s) and g(tu)=t·g(u)+g(t) give the full sum φ(s·f(t),st·g(u))−φ(s·f(t)+f(s),st·g(u))+φ(f(s),st·g(u)+s·g(t))−φ(f(s),s·g(t)), which is zero by bilinearity.
4. Choose finite witness fields F_f and F_g for f and g and take F=E₀⊔F_f⊔F_g. This compositum is finite-dimensional over ℚ. If r(k) and r(l) fix F, then f(sk)=f(s), g(tl)=g(t), and k acts trivially on B. Thus e₁(sk,tl)=φ(f(s),s·(k·g(t)))=e₁(s,t). This makes e₁ an actual level two-cocycle. All three constructions are bilinear before taking classes; addition and scalar multiplication can be checked pointwise, using a common finite compositum for levels.
5. For the (0,2) product, changing z by d₁u for a level one-cochain u changes e₀ by d₁(t↦φ(m,u(t))). The primitive is level by postcomposition. For the (2,0) product the corresponding primitive is t↦φ(u(t),d). Hence both endpoint products annihilate the exact denominator defining continuousH2, namely level coboundaries pulled back to level cocycles. Their bilinear maps therefore descend to the required H² inputs.
6. For the (1,1) product, if f=d₀a, let v(t)=φ(a,g(t)). The one-cocycle identity for g and equivariance give d₁v(s,t)=φ(s·a−a,s·g(t))=e₁(s,t). This primitive is level because g is level. If instead g=d₀b and f is a one-cocycle, put u(s)=φ(f(s),s·b). Direct expansion using f(st)=s·f(t)+f(s) gives d₁u(s,t)=−φ(f(s),s·(t·b−b))=−e₁(s,t). Refine the level of f with E₀. For k fixing that refinement, u(sk)=φ(f(s),s·(k·b))=u(s), so −u is a level primitive for e₁.
7. By the pinned H1π_eq_iff, equal ordinary H¹ classes of one-cocycles differ by d₀a for some a. Therefore Step 6 makes the product independent of either level representative of a continuousH1 class. Changing both representatives is handled successively. Every continuousH1 class has such a representative by its defining image formula. Bilinearity on representatives consequently gives a bilinear map on the two frozen continuousH1 carriers.
8. Use these descended maps as P₀,P₁,P₂, and curry each bilinear map into the displayed linear-map type. For each requested representative tuple, use the actual level two-cocycle constructed in Steps 1–4. The quotient construction and the descent in Steps 5–7 give exactly the three asserted class equalities. Indexing the three maps by Fin 3 only packages these already constructed maps.

## Key steps

1. Construct the three pointwise product functions and verify their two-cocycle equations.
2. Obtain actual level witnesses; the middle product uses a common field fixing B.
3. For the endpoint products, send level boundary primitives through equivariant linear maps.
4. For the middle product, use explicit level primitives for a boundary in either factor.
5. Use H1π_eq_iff and the continuousH2 quotient to descend bilinearly.
6. Return the three bilinear maps together with all representative witnesses.

## Reference use

### local-project

Queries:
- `rg -n 'def (continuousH|levelCo|IsTheta)|theorem.*(theta|transfer|cores)|normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup|H1π_eq|cupCochain' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory`
- `rg -n 'transfer|corestriction|prism|normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_Continuous*.lean .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology`
- `rg -n 'splittingField|finiteDimensional|Normal' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/Normal/Basic.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousDuality.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/Normal/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/Algebra/Group/Subgroup/Basic.lean`

The snapshot pins project 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. continuousH1 is the image of level one-cocycles in ordinary H1; continuousH2 is the quotient by the pulled-back image of level one-cochains. The theta predicates universally quantify over product-cocycle witnesses, so uniqueness needs actual witnesses. CupProduct supplies the middle product formula and explicit boundary primitives; LowDegree supplies H1π_eq_zero_iff and H1π_eq_iff. Normal/Basic supplies normality of splitting fields, and Subgroup/Basic supplies normality under comap. The focused continuous/cohomology search found no transfer, corestriction, prism implementation, or either policy-listed groupCohomology instance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
