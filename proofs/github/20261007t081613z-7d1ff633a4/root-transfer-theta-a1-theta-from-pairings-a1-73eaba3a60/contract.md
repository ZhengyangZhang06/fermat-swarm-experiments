<!-- theorem-id: fermat-p08/root.transfer_theta-a1.theta_from_pairings-a1 -->

## Theorem `Submission.p08_7d1ff633a4_tt26_theta_from_pairings`

Let k be a field, G a group, r : G → Autℚ(AlgebraicClosure ℚ) a homomorphism, A,B,N k-representations, and φ : A →ₗ[k] B →ₗ[k] N any bilinear map. Set X_i=Hⁱ(G,A), Y_i=H²⁻ⁱ(G,B), with H⁰ invariants and H¹,H² the frozen continuous carriers. Suppose bilinear maps P_i : X_i × Y_i → continuousH2 r N satisfy all three following conditions, where brackets mean the frozen representative maps. For every invariant m and level two-cocycle z of B there is a level two-cocycle e of N with e(s,t)=φ(m,z(s,t)) and P₀(m,[z])=[e]. For every pair of level one-cocycles f of A and g of B there is a level two-cocycle e with e(s,t)=φ(f(s),s·g(t)) and P₁([f],[g])=[e]. For every level two-cocycle z of A and invariant d of B there is a level two-cocycle e with e(s,t)=φ(z(s,t),d) and P₂([z],d)=[e]. Then for each linear ℓ : continuousH2 r N → k there is a family Θ_i : X_i → Y_i* satisfying IsTheta0 r φ ℓ (Θ₀), IsTheta1 r φ ℓ (Θ₁), and IsTheta2 r φ ℓ (Θ₂), with Θ_i(x)(y)=ℓ(P_i(x,y)). Every other family Ψ satisfying the same three predicates equals Θ degreewise. All duals are full algebraic duals; equivariance or a common stabilizing field is not additionally assumed in this conditional theorem.

Node: `root.transfer_theta-a1.theta_from_pairings-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/349

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_tt26_theta_from_pairings`

```lean
∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), let X : Fin 3 → ModuleCat k := ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 r A), ModuleCat.of k (groupCohomology.continuousH2 r A)]; let Y : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 r B), ModuleCat.of k (groupCohomology.continuousH1 r B), ModuleCat.of k B.ρ.invariants]; ∀ (P : ∀ i : Fin 3, X i →ₗ[k] Y i →ₗ[k] groupCohomology.continuousH2 r N), ((∀ (m : A.ρ.invariants) (z : groupCohomology.levelCocycles₂ r B), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ (m : A) ((z : G × G → B) st)) ∧ P 0 m (groupCohomology.continuousH2π r B z) = groupCohomology.continuousH2π r N e) ∧ (∀ (f : groupCohomology.cocycles₁ A) (hf : groupCohomology.IsLevelConstant₁ r (⇑f)) (g : groupCohomology.cocycles₁ B) (hg : groupCohomology.IsLevelConstant₁ r (⇑g)), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = groupCohomology.cupCochain φ (⇑f) (⇑g) st) ∧ P 1 ⟨(groupCohomology.H1π A).hom f, groupCohomology.H1π_mem_continuousH1 r A hf⟩ ⟨(groupCohomology.H1π B).hom g, groupCohomology.H1π_mem_continuousH1 r B hg⟩ = groupCohomology.continuousH2π r N e) ∧ (∀ (z : groupCohomology.levelCocycles₂ r A) (d : B.ρ.invariants), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ ((z : G × G → A) st) (d : B)) ∧ P 2 (groupCohomology.continuousH2π r A z) d = groupCohomology.continuousH2π r N e)) → ∀ ℓ : groupCohomology.continuousH2 r N →ₗ[k] k, ∃ Θ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i), (groupCohomology.IsTheta0 r φ ℓ (Θ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Θ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Θ 2)) ∧ (∀ (i : Fin 3) (x : X i) (y : Y i), Θ i x y = ℓ (P i x y)) ∧ (∀ Ψ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i), (groupCohomology.IsTheta0 r φ ℓ (Ψ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Ψ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Ψ 2)) → ∀ i : Fin 3, Ψ i = Θ i)
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
- Child DAG node: `root.transfer_theta-a1.theta_from_pairings-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix ℓ. For each i and x, define Θ_i(x) to be the functional y↦ℓ(P_i(x,y)). Linearity of P_i in its second argument and of ℓ makes this a member of the full algebraic dual. Linearity of P_i in its first argument makes x↦Θ_i(x) linear. This construction already gives the asserted evaluation formula.
2. Consider IsTheta0. Given m,z and any e satisfying its pointwise premise, the hypothesis on P₀ supplies a level cocycle e₀ with the same pointwise function and P₀(m,[z])=[e₀]. Function extensionality and subtype extensionality give e=e₀. Consequently Θ₀(m)([z])=ℓ([e₀])=ℓ([e]), as required for every e in the predicate.
3. For IsTheta1, given f,hf,g,hg and any e in its premise, the P₁ hypothesis supplies e₁ whose underlying function is precisely cupCochain φ f g. Thus e=e₁ by the same extensionality argument, and Θ₁([f])([g])=ℓ(P₁([f],[g]))=ℓ([e₁])=ℓ([e]). The continuousH1 subtype representatives are exactly those displayed in the frozen predicate; proof irrelevance identifies any membership proofs.
4. For IsTheta2, apply the P₂ hypothesis to z,d, identify its witness with the arbitrary e in the predicate by pointwise equality, and conclude Θ₂([z])(d)=ℓ([e]). Hence all three predicates hold.
5. Let Ψ satisfy the predicates. Every continuousH2 class is [z] for some level two-cocycle z, by surjectivity of the quotient map. For an invariant m and such a z, insert the supplied P₀ witness into IsTheta0 for Ψ. This gives Ψ₀(m)([z])=ℓ(P₀(m,[z]))=Θ₀(m)([z]), hence equality on every degree-zero input pair.
6. Every continuousH1 class has a level one-cocycle representative by the defining submodule-image formula. Choose such representatives for both degree-one inputs and insert the supplied P₁ witness into IsTheta1 for Ψ. It gives Ψ₁(x)(y)=ℓ(P₁(x,y))=Θ₁(x)(y) for every pair x,y.
7. Represent any degree-two first input as [z]; the second input is already invariant. Insert the P₂ witness into IsTheta2 for Ψ to obtain equality with Θ₂ on this pair. Thus equality holds on all pairs in all three degrees.
8. Extensionality of functionals and then of linear maps yields Ψ_i=Θ_i for i=0,1,2. These cases exhaust Fin 3, proving the asserted degreewise uniqueness.

## Key steps

1. Curry ℓ composed with each bilinear P_i into a map to the full dual.
2. Identify every universally quantified theta witness with the supplied actual product cocycle.
3. Use quotient surjectivity for H² and the image definition for H¹.
4. Evaluate any competing theta family on representatives and conclude by extensionality.

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

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/481

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
