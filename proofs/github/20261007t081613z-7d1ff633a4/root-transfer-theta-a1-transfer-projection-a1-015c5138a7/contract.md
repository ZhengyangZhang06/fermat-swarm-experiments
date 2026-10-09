<!-- theorem-id: fermat-p08/root.transfer_theta-a1.transfer_projection-a1 -->

## Theorem `Submission.p08_7d1ff633a4_tt26_transfer_projection`

Let k be a field, G a group, r : G → Autℚ(AlgebraicClosure ℚ) a homomorphism, and H≤G a finite-index subgroup. Let A,B,N be k-representations and E₀ a finite-dimensional normal rational intermediate field. Assume K₀=r⁻¹(Fix(E₀))≤H and K₀ acts trivially on A,B,N. Let φ : A →ₗ[k] B →ₗ[k] N be G-equivariant. For L=G,H use r_L=r or r restricted to H, the original representations restricted to L, and the same underlying φ_L. Write H⁰(L,V)=Vᴸ, H¹(L,V)=continuousH1 r_L(V|L), H²(L,V)=continuousH2 r_L(V|L). Put X_i=Hⁱ(G,A), Y_i=H²⁻ⁱ(G,B), XH_i=Hⁱ(H,A), YH_i=H²⁻ⁱ(H,B). Suppose bilinear families P_i : X_i×Y_i→H²(G,N) and PH_i : XH_i×YH_i→H²(H,N) have the following representative properties in their respective group L. Every invariant m and level two-cocycle z of B have a level product cocycle e(s,t)=φ_L(m,z(s,t)) representing P_L,0(m,[z]); every pair of level one-cocycles f,g has a level product cocycle e(s,t)=φ_L(f(s),s·g(t)) representing P_L,1([f],[g]); every level two-cocycle z of A and invariant d of B have a level product cocycle e(s,t)=φ_L(z(s,t),d) representing P_L,2([z],d). Here P_G=P and P_H=PH, and brackets are the frozen representative maps. Then there exist linear families RX_i:X_i→XH_i, CX_i:XH_i→X_i, RY_i:Y_i→YH_i, CY_i:YH_i→Y_i and RN:H²(G,N)→H²(H,N), CN:H²(H,N)→H²(G,N), such that CX_i(RX_i x)=[G:H]·x, CY_i(RY_i y)=[G:H]·y and CN(RN z)=[G:H]·z. The same chosen maps satisfy CN(PH_i(RX_i x,y′))=P_i(x,CY_i y′) and CN(PH_i(x′,RY_i y))=P_i(CX_i x′,y) for all degrees and arguments. No invertibility of the index, normality of H, or duality assumption is required.

Node: `root.transfer_theta-a1.transfer_projection-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/349

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/425

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/472, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/474, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/475, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/476

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_tt26_transfer_projection`

```lean
∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (H : Subgroup G) [H.FiniteIndex] (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E₀ → Normal ℚ E₀ → E₀.fixingSubgroup.comap r ≤ H → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ a : A, A.ρ g a = a) → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ g b = b) → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ z : N, N.ρ g z = z) → ∀ φ : A →ₗ[k] B →ₗ[k] N, (∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)) → let rH := r.comp H.subtype; let AH := Rep.res H.subtype A; let BH := Rep.res H.subtype B; let NH := Rep.res H.subtype N; let φH : AH →ₗ[k] BH →ₗ[k] NH := φ; let X : Fin 3 → ModuleCat k := ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 r A), ModuleCat.of k (groupCohomology.continuousH2 r A)]; let Y : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 r B), ModuleCat.of k (groupCohomology.continuousH1 r B), ModuleCat.of k B.ρ.invariants]; let XH : Fin 3 → ModuleCat k := ![ModuleCat.of k AH.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 rH AH), ModuleCat.of k (groupCohomology.continuousH2 rH AH)]; let YH : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 rH BH), ModuleCat.of k (groupCohomology.continuousH1 rH BH), ModuleCat.of k BH.ρ.invariants]; ∀ (P : ∀ i : Fin 3, X i →ₗ[k] Y i →ₗ[k] groupCohomology.continuousH2 r N) (PH : ∀ i : Fin 3, XH i →ₗ[k] YH i →ₗ[k] groupCohomology.continuousH2 rH NH), ((∀ (m : A.ρ.invariants) (z : groupCohomology.levelCocycles₂ r B), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ (m : A) ((z : G × G → B) st)) ∧ P 0 m (groupCohomology.continuousH2π r B z) = groupCohomology.continuousH2π r N e) ∧ (∀ (f : groupCohomology.cocycles₁ A) (hf : groupCohomology.IsLevelConstant₁ r (⇑f)) (g : groupCohomology.cocycles₁ B) (hg : groupCohomology.IsLevelConstant₁ r (⇑g)), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = groupCohomology.cupCochain φ (⇑f) (⇑g) st) ∧ P 1 ⟨(groupCohomology.H1π A).hom f, groupCohomology.H1π_mem_continuousH1 r A hf⟩ ⟨(groupCohomology.H1π B).hom g, groupCohomology.H1π_mem_continuousH1 r B hg⟩ = groupCohomology.continuousH2π r N e) ∧ (∀ (z : groupCohomology.levelCocycles₂ r A) (d : B.ρ.invariants), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ ((z : G × G → A) st) (d : B)) ∧ P 2 (groupCohomology.continuousH2π r A z) d = groupCohomology.continuousH2π r N e)) → ((∀ (m : AH.ρ.invariants) (z : groupCohomology.levelCocycles₂ rH BH), ∃ e : groupCohomology.levelCocycles₂ rH NH, (∀ st : H × H, (e : H × H → NH) st = φH (m : AH) ((z : H × H → BH) st)) ∧ PH 0 m (groupCohomology.continuousH2π rH BH z) = groupCohomology.continuousH2π rH NH e) ∧ (∀ (f : groupCohomology.cocycles₁ AH) (hf : groupCohomology.IsLevelConstant₁ rH (⇑f)) (g : groupCohomology.cocycles₁ BH) (hg : groupCohomology.IsLevelConstant₁ rH (⇑g)), ∃ e : groupCohomology.levelCocycles₂ rH NH, (∀ st : H × H, (e : H × H → NH) st = groupCohomology.cupCochain φH (⇑f) (⇑g) st) ∧ PH 1 ⟨(groupCohomology.H1π AH).hom f, groupCohomology.H1π_mem_continuousH1 rH AH hf⟩ ⟨(groupCohomology.H1π BH).hom g, groupCohomology.H1π_mem_continuousH1 rH BH hg⟩ = groupCohomology.continuousH2π rH NH e) ∧ (∀ (z : groupCohomology.levelCocycles₂ rH AH) (d : BH.ρ.invariants), ∃ e : groupCohomology.levelCocycles₂ rH NH, (∀ st : H × H, (e : H × H → NH) st = φH ((z : H × H → AH) st) (d : BH)) ∧ PH 2 (groupCohomology.continuousH2π rH AH z) d = groupCohomology.continuousH2π rH NH e)) → ∃ (RX : ∀ i : Fin 3, X i →ₗ[k] XH i) (CX : ∀ i : Fin 3, XH i →ₗ[k] X i) (RY : ∀ i : Fin 3, Y i →ₗ[k] YH i) (CY : ∀ i : Fin 3, YH i →ₗ[k] Y i) (RN : groupCohomology.continuousH2 r N →ₗ[k] groupCohomology.continuousH2 rH NH) (CN : groupCohomology.continuousH2 rH NH →ₗ[k] groupCohomology.continuousH2 r N), (∀ (i : Fin 3) (x : X i), CX i (RX i x) = (H.index : k) • x) ∧ (∀ (i : Fin 3) (y : Y i), CY i (RY i y) = (H.index : k) • y) ∧ (∀ z : groupCohomology.continuousH2 r N, CN (RN z) = (H.index : k) • z) ∧ (∀ (i : Fin 3) (x : X i) (y : YH i), CN (PH i (RX i x) y) = P i x (CY i y)) ∧ (∀ (i : Fin 3) (x : XH i) (y : Y i), CN (PH i x (RY i y)) = P i (CX i x) y)
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
- Child DAG node: `root.transfer_theta-a1.transfer_projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Use finite-dimensional normal rational intermediate fields E containing E₀ as common levels, and put K_E=r⁻¹(Fix(E)). The normal_kernel sibling proves that K_E is normal and finite-index in G. Fixing subgroups are antitone in fields, so K_E≤K₀≤H and K_E acts trivially on all three coefficients. Inside H the inverse image of Fix(E) under r restricted to H is exactly K_E viewed as a subgroup of H.
2. These common levels are cofinal among all finite collections of frozen witness fields. Indeed, take rational bases of those fields and E₀ and form the product of their minimal polynomials. In the algebraic closure let E be the field generated by all roots of this product. The product is nonzero and has finitely many algebraic roots, so E is finite-dimensional; it is a splitting field, hence normal. It contains every chosen basis and thus every witness field and E₀. Inverse-image fixing subgroups shrink on this refinement, so all original one-variable and two-variable level conditions remain true. Conversely every such E is an allowed frozen witness. The identical argument applies inside H. This is also the finite-normal-refinement argument used in the parent proof.
3. For L=G or H and a coefficient V, form homogeneous degree-j cochains F:L^(j+1)→V that are L-equivariant for simultaneous left translation and invariant under independent right K_E multiplication in each coordinate for some common level E. Addition uses a common refinement; scalar multiplication and zero preserve levels, giving vector spaces. Define δ by the alternating sum of coordinate deletions. Deletion preserves equivariance and levels. In δ² the term deleting original positions a<b has the two signs (−1)^(a+b−1) and (−1)^(a+b), so every term cancels.
4. Identify these with inhomogeneous cochains by F(g₀,…,g_j)=g₀·f(g₀⁻¹g₁,…,g_(j−1)⁻¹g_j), with inverse f(s₁,…,s_j)=F(1,s₁,s₁s₂,…,s₁⋯s_j). Consecutive differences and partial products prove that these linear formulas are inverse, using equivariance for the leading g₀-action. For level preservation, replacing g_i by g_i k_i changes each difference d to k_(i−1)⁻¹ d k_i∈dK_E, and the extra k₀-action on V is trivial. Conversely, replacing each s_i by s_i k_i changes the partial products only within their original right K_E-cosets: if an altered partial product is u_i h_i, the next is u_i s_(i+1)(s_(i+1)⁻¹h_i s_(i+1))k_(i+1), and normality puts the last two factors in K_E. Induction proves the claim. Degree-zero vectors correspond to g↦g·v, all of which have level E₀.
5. Define cohomology of this complex by cycles modulo boundaries in positive degrees and by ker δ in degree zero. Evaluating the deletion differential on (1,s), (1,s,st), and (1,s,st,stu) gives s·v−v, s·f(t)−f(st)+f(s), and s·z(t,u)−z(st,u)+z(s,tu)−z(s,t). These are precisely the pinned d₀₁,d₁₂,d₂₃. Degree-zero cohomology is therefore Vᴸ.
6. Every ordinary one-boundary d₀₁v is level, since d₀₁v(sk)=s·(k·v)−v=d₀₁v(s) for k∈K₀. The pinned H1π_eq_zero_iff and H1π_eq_iff show that the quotient of level one-cocycles by these boundaries maps injectively to ordinary H¹, with image exactly continuousH1 by its defining image formula. This yields a linear identification preserving the representative map.
7. Two-cycles are exactly levelCocycles₂. If f is a level one-cochain, refine with E₀ to a normal common K_E. For k,l∈K_E, f(sk)=f(s), f(tl)=f(t), sk acts on V as s does, and sktl=st(t⁻¹kt)l∈stK_E. Consequently d₁₂f(sk,tl)=d₁₂f(s,t). Its ordinary differential is zero by δ²=0, so these boundaries are level two-cocycles. Their image is exactly levelCoboundaries₂. Pulling this image back along the level-cocycle subtype gives exactly the denominator in continuousH2. The resulting linear identification preserves continuousH2π and uses no embedding into ordinary H².
8. On the ambient vertex set G form C_H^j(G,V), consisting of H-equivariant functions with the same common levels and deletion differential. Let j:H→G be inclusion. Choose representatives t of right cosets Ht, with representative 1 for H, and write g=ht uniquely. Set a(g)=h. Then a(h₁g)=h₁a(g) and a|H=id. If k∈K_E, gk=h(tkt⁻¹)t, so a(gk)=a(g)(tkt⁻¹), preserving right K_E-cosets. Hence coordinate restriction j* and precomposition a* preserve equivariance, levels, linearity and δ, and j*a*=id on H-domain cochains.
9. Prove the other composite is homotopic to the identity. For vertex maps α,β let P_j[g₀,…,g_j]=Σ_(i=0)^j(−1)^i[αg₀,…,αg_i,βg_i,…,βg_j]. In ∂P+P∂, deleting αg_l for l<i pairs with deleting original vertex l first and transition i−1; their signs are (−1)^(i+l) and (−1)^(l+i−1). Deleting βg_l for l>i pairs with deleting vertex l first and transition i; the signs are (−1)^(i+l+1) and (−1)^(l+i). At each internal transition, deletion of αg_i cancels deletion of βg_(i−1) in the preceding term. Only the all-β simplex minus the all-α simplex remains. In degree zero this is directly ∂[αg₀,βg₀]=[βg₀]−[αg₀], with ∂ zero on vertices.
10. Set α=j∘a and β=id. They are H-equivariant and preserve every right K_E-coset. Evaluation on the prisms defines a linear degree-lowering h preserving levels and equivariance; a duplicated vertex is handled by applying independent coordinate invariance to its two occurrences successively. Set h=0 in degree zero. Step 9 gives δh+hδ=id−a*j*. For positive-degree cocycles the difference is a boundary; for zero-cocycles it is zero. Thus j* and a* induce inverse cohomology maps.
11. Choose representatives t of the finitely many left cosets tH and define T_VF(g₀,…,g_j)=Σ_t t·F(t⁻¹g₀,…,t⁻¹g_j). A replacement t↦th leaves the summand unchanged, since H-equivariance cancels h against precomposition by h⁻¹. To check G-equivariance, reindex left cosets by s∈G and write t=st′h; the summand at (sg₀,…,sg_j) becomes s·(t′·F(t′⁻¹g₀,…,t′⁻¹g_j)). Thus T_V is G-equivariant. Right multiplication of one input by k∈K_E leaves every summand unchanged. Finite sums and coefficient actions prove linearity and commutation with δ.
12. Let I include G-equivariant cochains into the ambient H-equivariant ones. For G-equivariant F every summand of T_VIF equals F, so T_VI=[G:H]·id. Define restriction on cohomology as R_V=j*I and transfer as C_V=T_Va*. Using a*j*=id on cohomology gives C_VR_V=T_Va*j*I=T_VI=[G:H]·id. The scalar is the image in k of the number of left cosets; inversion identifies left and right coset sets. Transport these maps to the frozen carriers via Steps 5–7.
13. For homogeneous cochains of degrees a,b define (F∪Q)(g₀,…,g_(a+b))=φ(F(g₀,…,g_a),Q(g_a,…,g_(a+b))). Equivariance of φ gives equivariance, and common refinement gives a level; at the shared coordinate both factors remain unchanged. The operation is bilinear. Expanding coordinate deletion gives δ(F∪Q)=δF∪Q+(−1)^a F∪δQ: the two unmatched transition terms have identical value φ(F(g₀,…,g_a),Q(g_(a+1),…,g_(a+b+1))) and opposite signs (−1)^(a+1),(−1)^a. All other terms are exactly the deletions in the displayed formula.
14. Products of cocycles are cocycles. For a boundary in the first factor and a closed second factor, δP∪Q=δ(P∪Q). For a closed first factor and a boundary second factor, F∪δP=(−1)^aδ(F∪P). The primitives remain level by common refinement. Thus the products descend to cohomology; degree zero has no boundaries, so no negative-degree primitive is used. Coordinate precomposition preserves the product formula, so j*,a*,I preserve products.
15. Under the identifications of Steps 4–7 the product representatives in degrees (0,2),(1,1),(2,0) are exactly φ(m,z(s,t)), φ(f(s),s·g(t)), and φ(z(s,t),d). The invariant degree-zero representative is constant; in the middle case the second homogeneous factor at (s,st) is s·g(t); in the last case (st)·d=d. Therefore these transported cup products equal the supplied P and PH: their supplied level-cocycle witnesses have exactly the same underlying functions, hence are the same subtype elements. Every H² class has a quotient representative, every continuousH1 class has a level one-cocycle representative, and H⁰ consists of invariants. Equality on these representatives gives equality on all inputs.
16. Both projection formulas hold already on ambient cochains. For G-equivariant F and H-equivariant Q, equivariance of φ and F rewrites T_N((IF)∪Q) as Σ_t φ(F(g₀,…,g_a),t·Q(t⁻¹g_a,…,t⁻¹g_(a+b)))=F∪T_BQ by linearity in the second argument. For H-equivariant F and G-equivariant Q it gives Σ_t φ(t·F(t⁻¹g₀,…,t⁻¹g_a),Q(g_a,…,g_(a+b)))=T_AF∪Q by linearity in the first argument. No factor is interchanged.
17. Pass to cohomology. Since a* is product-preserving and a*j*=id there, a*(R_Ax∪y′)=Ix∪a*y′ and a*(x′∪R_By)=a*x′∪Iy. Apply T_N and Step 16 to obtain C_N(R_Ax∪y′)=x∪C_By′ and C_N(x′∪R_By)=C_Ax′∪y. Step 15 identifies these with exactly the two formulas for P,PH in the statement.
18. For A use R_A,C_A in degrees 0,1,2 as RX,CX; for B use R_B,C_B in degrees 2,1,0 as RY,CY; for N use their degree-two maps as RN,CN. Step 12 gives all scalar-composite identities and Step 17 gives both projection identities for the same maps. ModuleCat.of retains the original module structures, and restriction retains the underlying coefficient modules and φ. These facts give precisely the indexed Lean types, without any index inverse, normality of H, or duality hypothesis.

## Key steps

1. Refine all frozen levels to normal finite-index K_E contained in H and acting trivially.
2. Construct homogeneous level complexes and identify degrees 0,1,2 with the exact frozen carriers.
3. Use a right-coset retraction and the explicit prism identity to compare H-domain and ambient complexes.
4. Average over left cosets to construct transfer, proving transfer after restriction is the index scalar.
5. Descend homogeneous products and identify them with the supplied representative-specified P and PH.
6. Prove both ambient projection formulas and transport them to the frozen carriers.
7. Package the same chosen maps in degrees 0,1,2 and 2,1,0.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/563

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
