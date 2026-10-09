<!-- theorem-id: fermat-p08/root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1 -->

## Theorem `Submission.p08_7d1ff633a4_tt26_cp_one_one`

Let k be a field, G a group, Ω=AlgebraicClosure ℚ, r:G→Autℚ(Ω) a group homomorphism, and A,B,N k-representations of G. Let E₀ be a rational intermediate field in Ω, finite-dimensional over ℚ, such that r(s)∈Fix(E₀) implies s·b=b for every b∈B. Suppose φ:A→ₗ[k]B→ₗ[k]N is equivariant: φ(s·a,s·b)=s·φ(a,b). Write H¹(V)=continuousH1 r V, H²(V)=continuousH2 r V, Z²lev(V)=levelCocycles₂ r V, and πV=continuousH2π r V. A one-cocycle f is level when some finite-dimensional rational intermediate field F satisfies f(sh)=f(s) whenever r(h) fixes F; write [f]₁ for its ordinary H¹ class regarded as an element of the frozen image H¹(V). There exists a bilinear map P:H¹(A)×H¹(B)→H²(N) such that for every pair of level one-cocycles f of A and g of B, there is e∈Z²lev(N) satisfying e(s,t)=φ(f(s),s·g(t)) for all s,t∈G and P([f]₁,[g]₁)=πN(e). Neither normality nor finite index is assumed.

Node: `root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/426

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/535, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/536, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/539

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_tt26_cp_one_one`

```lean
∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E₀ → (∀ s : G, r s ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ s b = b) → ∀ φ : A →ₗ[k] B →ₗ[k] N, (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∃ P : groupCohomology.continuousH1 r A →ₗ[k] groupCohomology.continuousH1 r B →ₗ[k] groupCohomology.continuousH2 r N, ∀ (f : groupCohomology.cocycles₁ A) (hf : groupCohomology.IsLevelConstant₁ r (⇑f)) (g : groupCohomology.cocycles₁ B) (hg : groupCohomology.IsLevelConstant₁ r (⇑g)), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = groupCohomology.cupCochain φ (⇑f) (⇑g) st) ∧ P ⟨(groupCohomology.H1π A).hom f, groupCohomology.H1π_mem_continuousH1 r A hf⟩ ⟨(groupCohomology.H1π B).hom g, groupCohomology.H1π_mem_continuousH1 r B hg⟩ = groupCohomology.continuousH2π r N e
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

- Parent DAG node: `root.transfer_theta-a1.cup_pairings-a1`
- Child DAG node: `root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write d₀a(s)=s·a−a, d₁v(s,t)=s·v(t)−v(st)+v(s), and d₂z(s,t,u)=s·z(t,u)−z(st,u)+z(s,tu)−z(s,t). For level one-cocycles f of A and g of B, define e(f,g)(s,t)=φ(f(s),s·g(t)), the frozen cupCochain formula.
2. The one-cocycle identities are f(st)=s·f(t)+f(s) and g(tu)=t·g(u)+g(t). Equivariance and the representation law expand d₂e(f,g)(s,t,u) as φ(s·f(t),st·g(u))−φ(s·f(t)+f(s),st·g(u))+φ(f(s),st·g(u)+s·g(t))−φ(f(s),s·g(t)). Expanding both sums by bilinearity cancels every term. Thus e(f,g) is a two-cocycle.
3. Choose finite-dimensional witness fields Ff and Fg for f and g, and put F=(E₀⊔Ff)⊔Fg. Finite composita of finite-dimensional intermediate fields are finite-dimensional. If r(h) and r(l) fix F, they fix its three constituent fields. Consequently f(sh)=f(s), g(tl)=g(t), and h acts trivially on every vector of B. The representation law now gives e(f,g)(sh,tl)=φ(f(s),s·(h·g(t)))=φ(f(s),s·g(t)). Hence e(f,g) is an actual member of levelCocycles₂ r N. Denote its continuous H² class by Q(f,g).
4. The underlying functions satisfy e(f+f′,g)=e(f,g)+e(f′,g), e(c·f,g)=c·e(f,g), e(f,g+g′)=e(f,g)+e(f,g′), and e(f,c·g)=c·e(f,g), by linearity of φ and each representation operator. Sums of level one-cocycles are level using the finite compositum of their witness fields, and scalar multiples preserve their witness. Equality of the underlying functions is equality of the level-cocycle subtypes. Since continuousH2π is linear, Q satisfies these four bilinearity identities on level one-cocycles.
5. Suppose f=d₀a as functions for some a∈A. Define v(t)=φ(a,g(t)); it is level with the same witness as g. Equivariance and g(st)=s·g(t)+g(s) give d₁v(s,t)=φ(s·a,s·g(t))−φ(a,s·g(t)+g(s))+φ(a,g(s))=φ(s·a−a,s·g(t))=e(f,g)(s,t). Thus e(f,g) is the differential of a level one-cochain. By the defining denominator of continuousH2, Q(f,g)=0.
6. Suppose instead g=d₀b as functions for some b∈B. Put u(s)=φ(f(s),s·b). Equivariance and the cocycle identity for f give d₁u(s,t)=φ(s·f(t),st·b)−φ(s·f(t)+f(s),st·b)+φ(f(s),s·b)=−φ(f(s),s·(t·b−b))=−e(f,g)(s,t). The field E₀⊔Ff witnesses that u is level: if r(h) fixes this field, then f(sh)=f(s) and h·b=b, so u(sh)=φ(f(s),s·(h·b))=u(s). Its negative is also level, and d₁(−u)=e(f,g). Therefore Q(f,g)=0 in this case as well.
7. If level one-cocycles f,f′ have the same ordinary H¹ class, the pinned H1π_eq_iff says f−f′ is a one-coboundary, so f−f′=d₀a for some a. Their difference is a level one-cocycle, since levels are closed under subtraction using a common finite compositum. By Step 4 and Step 5, Q(f,g)−Q(f′,g)=Q(f−f′,g)=0. Similarly, if level g,g′ have the same ordinary H¹ class, Step 6 gives Q(f,g)−Q(f,g′)=Q(f,g−g′)=0. Changing the two representatives successively proves independence in both variables.
8. By its frozen definition as the image of levelCocycles₁ under (H1π).hom, every x∈continuousH1 r A is represented by some level f, and every y∈continuousH1 r B by some level g. Define P(x,y)=Q(f,g); Step 7 proves that this is well-defined on the stated image subtypes. To verify additivity in the first variable, choose level representatives f,f′ of x,x′ and g of y. Then f+f′ represents x+x′, and Step 4 gives P(x+x′,y)=P(x,y)+P(x′,y). The representative c·f similarly gives P(c·x,y)=c·P(x,y). Using g+g′ and c·g proves the corresponding two identities in the second variable. Curry this bilinear function to obtain the asserted linear map continuousH1 r A →ₗ[k] continuousH1 r B →ₗ[k] continuousH2 r N.
9. For any specified f,hf,g,hg, the subtype elements displayed in the statement are precisely their ordinary H¹ classes equipped with their image-membership proofs. Use e(f,g) from Steps 1–3 as the required level two-cocycle. Its pointwise formula is cupCochain φ f g, and Steps 7–8 ensure that P evaluated at those exact subtype classes equals continuousH2π r N e(f,g), independently of any chosen representatives or membership proofs. This gives both required conclusions.

## Key steps

1. Expand the cup cochain differential and cancel its terms using equivariance and the two one-cocycle identities.
2. Use the finite compositum of E₀ and the two level witness fields to obtain an actual level two-cocycle.
3. Prove bilinearity on level one-cocycles by pointwise calculation.
4. For a left coboundary d₀a, use the level primitive t↦φ(a,g(t)).
5. For a right coboundary d₀b, use the level primitive s↦−φ(f(s),s·b), refining the level field by E₀.
6. Apply H1π_eq_iff to show independence of each level representative.
7. Use the continuous H¹ image formula to define the pairing, prove bilinearity, and obtain the required representative equality.

## Reference use

### local-project

Queries:
- `rg -n 'continuous.*[Cc]up|[Cc]up.*continuous|normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory`
- `rg -n 'H1π_eq_iff|d₁₂_hom_apply|mem_cocycles₂_iff|d₂₃_hom_apply' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `rg -n 'finiteDimensional.*[Ss]up|[Ss]up.*finiteDimensional' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/IntermediateField`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2Map.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`

The manifest pins project 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. continuousH1 is the image of level one-cocycles under ordinary H1π; continuousH2 is the quotient of level two-cocycles by the pulled-back image of level one-cochains. ContinuousH2Map supplies equivariant postcomposition and preservation of this exact denominator. CupProduct supplies the ordinary cup cocycle and the two boundary-primitive calculations, but the focused search found no continuous cup-pairing descent. H1π_eq_iff identifies equal H¹ classes by coboundary differences; finiteDimensional_sup supplies the common finite levels. The focused search also found neither policy-listed instance. The four project definition files match the snapshot byte-for-byte; the local mathlib checkout is clean at the pinned revision. Diagnostic Lean axiom checks of continuousH2Map, H1π_eq_iff, cup, and continuousH2π_eq_zero_iff found only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/606

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
