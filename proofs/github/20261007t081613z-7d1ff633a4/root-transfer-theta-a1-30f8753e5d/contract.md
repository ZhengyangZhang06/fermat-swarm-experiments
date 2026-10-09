<!-- theorem-id: fermat-p08/root.transfer_theta-a1 -->

## Theorem `Submission.p08_7d1ff633a4_transfer_theta`

Let k be a field, G a group, r : G → Aut(AlgebraicClosure ℚ/ℚ) a group homomorphism, and H ≤ G a finite-index subgroup. Let A, B, N be k-linear representations of G. Suppose E₀ is a finite-dimensional normal rational intermediate field, K₀ = r⁻¹(Fix(E₀)) lies in H, and K₀ acts trivially on A, B, N. Let φ : A →ₗ[k] B →ₗ[k] N be G-equivariant. Define H⁰(L,V) as invariants, H¹(L,V) as the frozen continuousH1, and H²(L,V) as the frozen continuousH2, using r restricted to L and the original coefficients restricted to L. For i = 0,1,2 put X_i = Hⁱ(G,A), Y_i = H²⁻ⁱ(G,B), XH_i = Hⁱ(H,A), YH_i = H²⁻ⁱ(H,B). There exist linear maps RX_i : X_i → XH_i, CX_i : XH_i → X_i, RY_i : Y_i → YH_i, CY_i : YH_i → Y_i, RN : H²(G,N) → H²(H,N), and CN : H²(H,N) → H²(G,N), satisfying CX_i RX_i = ([G:H] : k) id, CY_i RY_i = ([G:H] : k) id, and CN RN = ([G:H] : k) id. These maps can be chosen so that, for every linear ℓ : H²(G,N) → k, there exist families Θ_i : X_i → Y_i* and ΘH_i : XH_i → YH_i* satisfying the three frozen theta predicates over G with φ and ℓ, and over H with restricted φ and ℓ ∘ CN. Every other G-family satisfying those predicates equals Θ degreewise. Furthermore, ΘH_i(RX_i x)(y′) = Θ_i(x)(CY_i y′) and ΘH_i(x′)(RY_i y) = Θ_i(CX_i x′)(y) for all arguments. The duals are full algebraic duals. No invertibility of the index, normality of H, or duality hypothesis is assumed.

Node: `root.transfer_theta-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/347

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/425, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/426, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/427, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/428

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_transfer_theta`

```lean
∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (H : Subgroup G) [H.FiniteIndex] (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E₀ → Normal ℚ E₀ → E₀.fixingSubgroup.comap r ≤ H → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ a : A, A.ρ g a = a) → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ g b = b) → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ z : N, N.ρ g z = z) → ∀ φ : A →ₗ[k] B →ₗ[k] N, (∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)) → let rH := r.comp H.subtype; let AH := Rep.res H.subtype A; let BH := Rep.res H.subtype B; let NH := Rep.res H.subtype N; let φH : AH →ₗ[k] BH →ₗ[k] NH := φ; let X : Fin 3 → ModuleCat k := ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 r A), ModuleCat.of k (groupCohomology.continuousH2 r A)]; let Y : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 r B), ModuleCat.of k (groupCohomology.continuousH1 r B), ModuleCat.of k B.ρ.invariants]; let XH : Fin 3 → ModuleCat k := ![ModuleCat.of k AH.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 rH AH), ModuleCat.of k (groupCohomology.continuousH2 rH AH)]; let YH : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 rH BH), ModuleCat.of k (groupCohomology.continuousH1 rH BH), ModuleCat.of k BH.ρ.invariants]; ∃ (RX : ∀ i : Fin 3, X i →ₗ[k] XH i) (CX : ∀ i : Fin 3, XH i →ₗ[k] X i) (RY : ∀ i : Fin 3, Y i →ₗ[k] YH i) (CY : ∀ i : Fin 3, YH i →ₗ[k] Y i) (RN : groupCohomology.continuousH2 r N →ₗ[k] groupCohomology.continuousH2 rH NH) (CN : groupCohomology.continuousH2 rH NH →ₗ[k] groupCohomology.continuousH2 r N), (∀ (i : Fin 3) (x : X i), CX i (RX i x) = (H.index : k) • x) ∧ (∀ (i : Fin 3) (y : Y i), CY i (RY i y) = (H.index : k) • y) ∧ (∀ z : groupCohomology.continuousH2 r N, CN (RN z) = (H.index : k) • z) ∧ ∀ ℓ : groupCohomology.continuousH2 r N →ₗ[k] k, ∃ (Θ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i)) (ΘH : ∀ i : Fin 3, XH i →ₗ[k] Module.Dual k (YH i)), (groupCohomology.IsTheta0 r φ ℓ (Θ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Θ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Θ 2)) ∧ (groupCohomology.IsTheta0 rH φH (ℓ.comp CN) (ΘH 0) ∧ groupCohomology.IsTheta1 rH φH (ℓ.comp CN) (ΘH 1) ∧ groupCohomology.IsTheta2 rH φH (ℓ.comp CN) (ΘH 2)) ∧ (∀ Ψ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i), (groupCohomology.IsTheta0 r φ ℓ (Ψ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Ψ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Ψ 2)) → ∀ i : Fin 3, Ψ i = Θ i) ∧ (∀ (i : Fin 3) (x : X i) (y : YH i), ΘH i (RX i x) y = Θ i x (CY i y)) ∧ (∀ (i : Fin 3) (x : XH i) (y : Y i), ΘH i x (RY i y) = Θ i (CX i x) y)
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
- Child DAG node: `root.transfer_theta-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data and write n = ([G:H] : k). For every finite-dimensional normal rational intermediate field E containing E₀, put K_E = E.fixingSubgroup.comap r. Choose a finite rational basis of E and take the union Z_E of the complete root sets of its minimal polynomials in AlgebraicClosure ℚ. Normality puts these roots in E. The finite set Z_E contains the basis and generates E. Rational automorphisms permute Z_E, and the action through r has kernel exactly K_E. Consequently K_E is normal and its cosets inject into a finite permutation group, proving finite index. Since E contains E₀, K_E ≤ K₀ ≤ H, and K_E acts trivially on all three coefficients.
2. The subgroups K_E give cofinal common levels. Given finitely many finite-dimensional witness fields, apply p08_7d1ff633a4_normal_refinement to them together with E₀. The resulting E contains each witness, so K_E is contained in every original inverse-image fixing subgroup. Constancy at an original level therefore implies constancy at K_E. Conversely, E is itself an allowed witness field. For r restricted to H, the preimage of E.fixingSubgroup is exactly K_E viewed inside H. This proves the same cofinality for both groups and for one-variable and two-variable level conditions. For auxiliary higher cochains, use independent right K_E-invariance in every coordinate.
3. For L = G or H and any coefficient V among A, B, N restricted to L, define degree-j homogeneous level cochains as functions F : L^(j+1) → V satisfying F(sg₀,…,sgⱼ) = s·F(g₀,…,gⱼ) and constant under independent right multiplication of coordinates by elements of some K_E. Common refinement proves closure under addition; scalar multiplication preserves a level, and zero has every level. Thus these form vector spaces.
4. Their correspondence with inhomogeneous level cochains is F(g₀,…,gⱼ) = g₀·f(g₀⁻¹g₁,g₁⁻¹g₂,…,gⱼ₋₁⁻¹gⱼ), with inverse f(s₁,…,sⱼ) = F(1,s₁,s₁s₂,…,s₁⋯sⱼ). Consecutive differences and partial products show that the formulas are inverse; equivariance supplies the leading g₀-action. Both formulas are linear. Replacing g_i by g_i k_i changes an adjacent difference d to k_(i−1)⁻¹ d k_i, which lies in dK_E by normality, and the extra action by k₀ is trivial. Conversely, if an altered partial product is u_i h_i with h_i ∈ K_E, then multiplying the next altered factor gives u_i h_i s_(i+1) k_(i+1) = u_i s_(i+1)(s_(i+1)⁻¹ h_i s_(i+1))k_(i+1), which lies in u_i s_(i+1)K_E. Induction proves that all altered partial products remain in their original right cosets. Thus both formulas preserve levels. In degree zero the correspondence is v ↦ (g ↦ g·v), which has level E₀ for every v.
5. Define δF as the alternating sum of deleting one coordinate. Deletion preserves equivariance and levels. In δ², deleting original positions a < b occurs twice with signs (−1)^(a+b−1) and (−1)^(a+b); these terms cancel, also in characteristic two. Hence δ² = 0. Define positive-degree cohomology as cycles modulo boundaries and degree-zero cohomology as the kernel of δ. Evaluation at (1,s), (1,s,st), and (1,s,st,stu) gives δv(s) = s·v−v, δf(s,t) = s·f(t)−f(st)+f(s), and δz(s,t,u) = s·z(t,u)−z(st,u)+z(s,tu)−z(s,t). These are exactly the pinned d₀₁, d₁₂, and d₂₃.
6. This cohomology has the required frozen carriers. In degree zero the kernel is exactly the invariant subspace. Every ordinary degree-one boundary δv is level: for k₀ ∈ K₀, δv(sk₀) = s·(k₀·v)−v = δv(s). The pinned H1π_eq_zero_iff and H1π_eq_iff identify the kernel of the map from one-cocycles to ordinary H¹ with these boundaries and characterize equality of classes by their difference being a boundary. Therefore the quotient of level one-cocycles embeds linearly in ordinary H¹ with image exactly the submodule continuousH1, by its defining image formula. This gives a linear identification preserving the representative map.
7. In degree two the cycles are exactly levelCocycles₂. If f is a level one-cochain, refine its level together with E₀ to K_E. For k,l ∈ K_E, f(tl) = f(t), f(sk) = f(s), sk acts as s on V, and sktl = st(t⁻¹kt)l lies in stK_E. The differential formula therefore gives δf(sk,tl) = δf(s,t). Thus all such boundaries are level two-cocycles, and they are exactly levelCoboundaries₂, the image of levelCochains₁ under d₁₂. Pulling this image back along the level-cocycle subtype gives precisely the denominator defining continuousH2. This proves the degree-two linear identification and preserves its representative map; no embedding into ordinary H² is needed.
8. Introduce the ambient-domain complex C_H^j(G,V) of H-equivariant functions on G^(j+1) with the same level condition and deletion differential. Inclusion j : H → G induces coordinate restriction j*. Choose representatives t of the right cosets Ht, choosing 1 for H. Write each g uniquely as ht and put a(g) = h. Then a(h₁g) = h₁a(g) and a is the identity on H. Coordinate precomposition defines a* in the reverse direction, with j*a* = id. If k ∈ K_E and g = ht, then gk = h(tkt⁻¹)t and a(gk) = a(g)(tkt⁻¹). Since K_E is normal and lies in H, this preserves the required right cosets. Thus a* preserves levels and equivariance. Restriction also preserves levels. Both maps are linear and commute with δ because coordinate precomposition commutes with deletion.
9. The other composite induces the identity on cohomology. For vertex maps α,β define the prism P_j[g₀,…,gⱼ] = Σ_(i=0)^j (−1)^i[αg₀,…,αg_i,βg_i,…,βgⱼ]. Its deletion boundary satisfies ∂P + P∂ = β_*−α_*, taking the boundary to be zero in degree zero. To verify this, deleting αg_l with l < i in the i-th prism term has sign (−1)^(i+l), whereas deleting that original vertex first and taking transition i−1 has sign (−1)^(l+i−1). Deleting βg_l with l > i has sign (−1)^(i+l+1), whereas its corresponding P∂ term has sign (−1)^(l+i). These pairs cancel. For i ≥ 1, deleting αg_i cancels deleting βg_(i−1) from the preceding prism term. The survivors are the all-β simplex and minus the all-α simplex; for j = 0 this is ∂[αg₀,βg₀] = [βg₀]−[αg₀].
10. Take α = j ∘ a and β = id. Both are H-equivariant and preserve right K_E-cosets. Evaluating cochains on the prism preserves equivariance and levels. When a vertex is duplicated, apply independent coordinate invariance successively to its two occurrences. This defines a degree-lowering map h in positive degrees, with h = 0 on degree zero, and gives δh+hδ = id−a*j*. For positive-degree cocycles the difference is a boundary, and for degree-zero cocycles it is zero. Thus j* and a* induce inverse cohomology maps.
11. Choose representatives t of the finitely many left cosets tH. For F ∈ C_H^j(G,V), define T_VF(g₀,…,gⱼ) = Σ_t t·F(t⁻¹g₀,…,t⁻¹gⱼ). Replacing t by th does not change a summand because H-equivariance cancels the action of h against precomposition by h⁻¹. For s ∈ G, reindex left cosets by multiplication by s and write a chosen representative as t = st′h. Its summand at (sg₀,…,sgⱼ) becomes s·(t′·F(t′⁻¹g₀,…,t′⁻¹gⱼ)). Summation proves G-equivariance. Replacing g_i by g_i k with k ∈ K_E replaces t⁻¹g_i by (t⁻¹g_i)k, so every summand is unchanged. Thus transfer preserves levels and is linear. It commutes with δ because finite sums and coefficient actions commute with deletion and signs.
12. Let I include G-equivariant cochains among H-equivariant cochains on G. It preserves levels and commutes with δ. For G-equivariant F, every summand of T_VIF equals F, so T_VI = n id. There are [G:H] summands; inversion identifies the left and right coset sets. On cohomology define restriction by j*I and transfer by T_Va*. Step 10 gives T_Va*j*I = T_VI on cohomology, hence transfer after restriction equals n id. Transport through Steps 6–7 and the degree-zero identification. Take the A-maps in degrees 0,1,2 as RX,CX; the B-maps in degrees 2,1,0 as RY,CY; and the N-maps in degree two as RN,CN. This proves all stated scalar-composite identities, with the maps chosen before ℓ.
13. For homogeneous cochains F,Q of degrees a,b on a common vertex set and with a common equivariance group, define (F ∪ Q)(g₀,…,g_(a+b)) = φ(F(g₀,…,g_a),Q(g_a,…,g_(a+b))). Equivariance of φ gives equivariance of the product. Common refinement gives its level: changing the shared coordinate preserves both factors, and changing any other coordinate preserves its affected factor. Bilinearity of φ gives bilinearity of the operation. Expanding the deletion differential yields δ(F∪Q) = δF∪Q + (−1)^a F∪δQ. Deletions at positions through a match the first term, and later deletions match the second. The two extra transition terms both have value φ(F(g₀,…,g_a),Q(g_(a+1),…,g_(a+b+1))) and have opposite signs (−1)^(a+1) and (−1)^a, so they cancel.
14. Products of cocycles are cocycles. If F = δP and Q is closed, then F∪Q = δ(P∪Q). If F is closed and Q = δP, then F∪Q = (−1)^aδ(F∪P). The displayed primitives remain level cochains by common refinement. Thus changing either representative by a boundary does not change the product class; changing both can be done successively. The products descend bilinearly to cohomology. Degree zero has no boundaries, so no negative-degree primitive is needed. Coordinate precomposition preserves the product formula, so j*, a*, and I preserve these products.
15. On ambient cochains both projection formulas hold. If F is G-equivariant and Q is H-equivariant, equivariance of φ and F rewrites T_N((IF)∪Q) at a tuple as Σ_t φ(F(g₀,…,g_a),t·Q(t⁻¹g_a,…,t⁻¹g_(a+b))). Linearity in the second argument gives F∪T_BQ. If F is H-equivariant and Q is G-equivariant, the sum instead becomes Σ_t φ(t·F(t⁻¹g₀,…,t⁻¹g_a),Q(g_a,…,g_(a+b))), which equals T_AF∪Q by linearity in the first argument. Pass to cohomology and use the product-preserving inverse maps j*,a*. In particular, a*(RX_i x∪y′) = Ix∪a*y′ and a*(x′∪RY_i y) = a*x′∪Iy, since a*j* is the identity there. Applying transfer gives CN(RX_i x∪y′) = x∪CY_i y′ and CN(x′∪RY_i y) = CX_i x′∪y. The factor order is unchanged, so no graded-commutativity sign occurs.
16. The inhomogeneous product representatives in degrees (0,2), (1,1), and (2,0) are respectively (s,t) ↦ φ(m,z(s,t)), (s,t) ↦ φ(f(s),s·g(t)), and (s,t) ↦ φ(z(s,t),d). For the first formula the homogeneous representative of invariant m is constant. For the second the homogeneous representative of g at (s,st) is s·g(t). For the third the final factor is initially (st)·d and equals d by invariance. These are exactly the functions in the frozen IsTheta0, IsTheta1, and IsTheta2 definitions, with the middle one equal to cupCochain. Steps 13–14 prove that each is an actual level two-cocycle and that its class depends bilinearly on the cohomology inputs.
17. For either L = G or H and any linear λ : H²(L,N) → k, define Θ_(L,i)(x)(y) = λ(x∪y). Bilinearity makes this a linear map into the full algebraic dual. Step 16 supplies a product cocycle for every representative pair in each theta predicate. Any other cocycle e satisfying that predicate's pointwise premise has the same underlying function as this product cocycle, hence equals it and has the same class. Thus the constructed maps satisfy the entire predicates, including their universal quantification over e.
18. The predicates determine these maps uniquely. For IsTheta0, insert the product witness for every invariant m and every level two-cocycle z; every H² class has such a representative by the quotient definition. For IsTheta1, both continuousH1 inputs have level one-cocycle representatives by the image definition, and inserting their product witness determines the value. For IsTheta2, represent its H² input by a level two-cocycle; its other input is already invariant. Hence every value on a pair of cohomology inputs is determined. Extensionality first of functionals and then of linear maps proves uniqueness. In particular, every G-family Ψ satisfying the three predicates equals the constructed family in each of the three degrees.
19. Given ℓ, take λ = ℓ over G and λ = ℓ ∘ CN over H. Denote the resulting families by Θ and ΘH. Their six predicates follow from Step 17. Applying ℓ to the first projection formula gives ΘH_i(RX_i x)(y′) = ℓ(CN(RX_i x∪y′)) = ℓ(x∪CY_i y′) = Θ_i(x)(CY_i y′). The second gives ΘH_i(x′)(RY_i y) = ℓ(CN(x′∪RY_i y)) = ℓ(CX_i x′∪y) = Θ_i(CX_i x′)(y). These are the required compatibilities.
20. Index the three A-degrees by Fin 3 in order 0,1,2 and the B-degrees in order 2,1,0. ModuleCat.of preserves their existing additive and k-module structures, so these maps have the exact indexed types stated. Restriction preserves underlying coefficient modules, making φH the same bilinear map as φ. Steps 12 and 17–19 provide all existential witnesses and conjunctions. The transfers were chosen independently of ℓ, and no argument used normality of H, invertibility of n, or bijectivity of a theta map.

## Key steps

1. Construct cofinal finite normal levels contained in H and trivializing all coefficients.
2. Identify homogeneous level cohomology with the exact frozen spaces in degrees zero, one, and two.
3. Compare subgroup and ambient-domain cochains using coset representatives and the prism homotopy.
4. Construct transfer by a finite coset sum and prove transfer after restriction is multiplication by the index.
5. Descend homogeneous cup products and establish both projection formulas.
6. Match product representatives with the frozen theta predicates and prove nonvacuous existence and uniqueness.
7. Apply ℓ and ℓ ∘ CN to obtain both theta compatibility identities.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
