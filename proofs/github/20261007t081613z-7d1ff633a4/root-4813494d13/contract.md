<!-- theorem-id: fermat-p08/root -->

## Theorem `groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen`

Prove `groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen` for `fermat-p08` using the exact frozen contract in `Fermat/Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.lean`. Write the Lean solution in Submission.lean. Use the issue/PR workflow: complete and independently review the natural-language proof, publish every new named helper as an issue, and require the controller comparator and independent review before a solution PR is merged and its issue closed. Workers independently poll issues; do not dispatch or notify other workers. No web search. Do not import the original upstream solution of this target. Pinned unchanged libraries may be reused with exact provenance and axiom checks.

Node: `root`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: None (root)

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/347, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/348, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/349, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/350, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/351

## Lean problem

Declaration: `groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen`

```lean
∀ {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (S : Subgroup (primeLocalGaloisGroup q)) (U : Subgroup S) [U.FiniteIndex] (hUp : IsUnit ((U.index : ℕ) : ZMod p)) (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ U) (hTU : FiniteDimensional (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) ∧ finrank (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) = 1) (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M] (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m) (inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p) (hinv : Function.Bijective inv) (hres : ∀ (invU : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) →ₗ[ZMod p] ZMod p), Function.Bijective invU → ∀ (θ₀ : (Rep.res U.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))), IsTheta0 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p] Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₀ → ∀ (θ₁ : continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))), IsTheta1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p] Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₁ → ∀ (θ₂ : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))).ρ.invariants), IsTheta2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p] Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₂ → Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂) (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)))) (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p] Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₀) (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)))) (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p] Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₁) (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants) (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p] Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₂), Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂
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

# Final proof of the open-subgroup theta descent theorem

This is the prose handoff for exactly
`groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen` in `Submission.lean`.
The frozen problem is the declaration in
`Fermat/Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.lean`
at source revision `9db4b2bea94e42612c675170cfe30ec626166658`.
The argument implements the accepted `natural-proof-v157.md`, using the current
approved child declarations. Historical plans and review records are unchanged.

## Assumptions and notation

1. Let `p` be a natural number with `Fact p.Prime`, let `q : Nat.Primes`, let
   `S ≤ primeLocalGaloisGroup q`, and let `U ≤ S` have finite index. Set
   `k = ZMod p`, `r = (primeLocalToGlobal q).comp S.subtype`,
   `χ = ((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype`,
   `D = M.dualTwist χ`, and
   `T = Rep.res S.subtype (ofChar ((cycloChar p).comp (primeLocalToGlobal q)))`.
   The prime hypothesis makes `k` a field. There is no assumption relating `p`
   and `q`, and `U` need not be normal. Write `H⁰(V) = V.ρ.invariants`,
   `H¹(V) = continuousH1 r V`, and `H²(V) = continuousH2 r V`. A subscript `U`
   means that both `r` and the original coefficient representation are
   restricted to `U`. All duals below are full algebraic linear duals.

2. Hypothesis `hUp` says that `n = (U.index : k)` is a unit, so `n ≠ 0`.
   Hypothesis `hU` supplies a finite-dimensional rational intermediate field
   whose fixing subgroup pulls back under `r` into `U`. The representation `M`
   is finite-dimensional over `k`, and `hsm` supplies, for each vector of `M`, a
   finite-dimensional rational intermediate field whose fixing preimage fixes
   that vector. Hypothesis `hTU` gives both finite-dimensionality and dimension
   one of `H²_U(T)`. The given linear functional `inv : H²(T) → k` is bijective
   by `hinv`.

3. The three supplied linear maps have domains and targets
   `θ₀ : H⁰(M) → H²(D)*`, `θ₁ : H¹(M) → H¹(D)*`, and
   `θ₂ : H²(M) → H⁰(D)*`. Hypotheses `hθ₀`, `hθ₁`, and `hθ₂` assert their
   respective frozen `IsTheta0`, `IsTheta1`, and `IsTheta2` predicates for the
   evaluation pairing and `inv`. Hypothesis `hres` says that for **every**
   bijective linear functional on `H²_U(T)` and every triple satisfying the
   corresponding three restricted predicates, all three maps are bijective.
   The required conclusion is the conjunction of bijectivity of the supplied
   `θ₀`, `θ₁`, and `θ₂`. No finite-dimensionality of any other cohomology space
   is assumed.

## Proof matching the Lean implementation

4. Apply `Submission.p08_7d1ff633a4_common_kernel` to `q, S, U, M, hU, hsm`.
   Its hypotheses are precisely the prime and finite-dimensionality instances,
   the finite-dimensional field witness in `hU`, and the vectorwise witness in `hsm`.
   It supplies a finite-dimensional normal rational intermediate field `E`
   such that `E.fixingSubgroup.comap r ≤ U`, and every element of this preimage
   acts trivially on each of `M`, `D`, and `T`. This is a proved child lemma,
   not an extra hypothesis of the root. Its accepted construction combines a
   common stabilizer field for a finite basis, a field killing the cyclotomic
   character, and the finite normal refinement lemma.

5. The underlying vector spaces of `D` and `T` are respectively `M*` and `k`.
   Their actions are `(s·d)(m) = χ(s) d(s⁻¹·m)` and `s·a = χ(s)a`.
   Let `φ = Module.Dual.eval k M`, so `φ(m,d) = d(m)`. Then
   `φ(s·m,s·d) = χ(s)d(s⁻¹·(s·m)) = χ(s)d(m) = s·φ(m,d)`.
   The middle equality follows from the representation homomorphism laws:
   `M.ρ s⁻¹ ∘ M.ρ s = M.ρ (s⁻¹*s) = id`. The Lean local fact `hφ` unfolds
   the coefficient actions and uses `Module.End.mul_apply`, `map_mul`,
   `inv_mul_cancel`, and `map_one`. Restriction leaves the underlying vector
   spaces and evaluation unchanged, including the twice-restricted `T` in
   `hTU` and `hres`.

6. Apply `Submission.p08_7d1ff633a4_transfer_theta` with field `k`, group `S`,
   homomorphism `r`, finite-index subgroup `U`, representations `M, D, T`,
   field `E`, and pairing `φ`. Step 4 provides its finite normal field,
   containment, and all three trivial-action hypotheses; Step 5 provides
   equivariance. For `i = 0,1,2` write
   `Xᵢ = Hⁱ(M)`, `Yᵢ = H²⁻ⁱ(D)`, and use the corresponding restricted spaces
   `XUᵢ`, `YUᵢ`. The child supplies linear maps
   `RXᵢ : Xᵢ → XUᵢ`, `CXᵢ : XUᵢ → Xᵢ`,
   `RYᵢ : Yᵢ → YUᵢ`, `CYᵢ : YUᵢ → Yᵢ`,
   `RN : H²(T) → H²_U(T)`, and `CN : H²_U(T) → H²(T)` satisfying
   `CXᵢ(RXᵢ x) = n x`, `CYᵢ(RYᵢ y) = n y`, and `CN(RN z) = n z`.

7. Define `invU = inv.comp CN`. Install the finite-dimensionality instance
   from `hTU.1`. Apply `Submission.p08_7d1ff633a4_rank_one_transfer` to
   `n`, its nonvanishing, `RN`, `CN`, the last scalar identity from Step 6,
   the dimension equality `hTU.2`, and the surjectivity `hinv.2` of `inv`.
   It proves that `invU` is bijective. To explain the linear-algebra content,
   choose `z` with `inv(z)=1`; then `v=n⁻¹ RN(z)` satisfies `invU(v)=1`.
   Thus `v` is nonzero and spans the one-dimensional domain of `invU`.
   Every vector is uniquely `a v`, and `invU(a v)=a`, proving bijectivity.
   This uses no finite-dimensionality assumption on `H²(T)`. The injectivity
   component of `hinv` is stronger than needed by this step; it remains in the
   unchanged frozen theorem statement.

8. Specialize the theta-producing part of Step 6 to `inv`. It supplies global
   maps `Θᵢ : Xᵢ → Yᵢ*` and restricted maps `ΘUᵢ : XUᵢ → YUᵢ*`, with the
   three theta predicates for each triple. The restricted functional is exactly
   `inv.comp CN`. Moreover, the global triple is unique among triples satisfying
   those predicates, and for all arguments it satisfies
   `ΘUᵢ(RXᵢ x)(yU) = Θᵢ(x)(CYᵢ yU)` and
   `ΘUᵢ(xU)(RYᵢ y) = Θᵢ(CXᵢ xU)(y)`.
   These are the two projection identities provided by the accepted transfer
   child; no choice of a new cohomology model or new duality assumption is made.

9. Apply `hres` to `invU`, its bijectivity from Step 7, and `ΘU₀, ΘU₁, ΘU₂`
   with the three predicate proofs from Step 8. It gives bijectivity of each
   `ΘUᵢ`. All its coefficients are restrictions of the original representations,
   exactly as in the frozen hypothesis.

10. Package the supplied maps into the dependent family `Ψ` on `Fin 3` using
    `Fin.cases`: its entries are `θ₀, θ₁, θ₂`, with the `ModuleCat` carriers
    `X = ![H⁰(M), H¹(M), H²(M)]` and `Y = ![H²(D), H¹(D), H⁰(D)]`.
    The hypotheses `hθ₀, hθ₁, hθ₂` prove the three predicates for this family.
    Apply the uniqueness statement from Step 8 to `Ψ`; evaluation at `0,1,2`
    gives `θ₀ = Θ₀`, `θ₁ = Θ₁`, and `θ₂ = Θ₂`. These equalities rewrite the
    requested conclusion to the three constructed global maps.

11. For each index apply `Submission.p08_7d1ff633a4_linear_descent` with
    spaces `Xᵢ, Yᵢ, XUᵢ, YUᵢ`, scalar `n ≠ 0`, the four maps from Step 6,
    the pairings `Θᵢ, ΘUᵢ`, the two scalar identities, the two projection
    identities from Step 8, and the restricted bijectivity from Step 9.
    These are all hypotheses of that child; it has no dimension hypotheses.
    Its injectivity argument is: if `Θᵢ(x)=0`, the first projection identity
    makes `ΘUᵢ(RXᵢ x)=0`; injectivity implies `RXᵢ x=0`, whence `n x=0`
    and `x=0`. Applying this to a difference proves injectivity. For surjectivity,
    given `λ ∈ Yᵢ*`, choose `xU` with `ΘUᵢ(xU)=λ.comp CYᵢ`. Then for every `y`,
    `Θᵢ(n⁻¹ CXᵢ xU)(y) = n⁻¹ ΘUᵢ(xU)(RYᵢ y)
     = n⁻¹ λ(CYᵢ(RYᵢ y)) = n⁻¹ λ(n y) = λ(y)`.
    Thus `Θᵢ` is surjective and bijective. The three applications and Step 10
    give exactly `Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂`.

## Dependency and integration provenance

The root directly applies four approved declarations, all in `Submission.lean`:
`Submission.p08_7d1ff633a4_common_kernel`,
`Submission.p08_7d1ff633a4_transfer_theta`,
`Submission.p08_7d1ff633a4_rank_one_transfer`, and
`Submission.p08_7d1ff633a4_linear_descent`.
The fifth listed dependency, `Submission.p08_7d1ff633a4_normal_refinement`, is
used transitively by common-kernel and transfer infrastructure. It is not
reproved or replaced in this root.

All 20 accepted child declarations remain present under their original global
names and types. The deeper accepted declarations provide the cyclotomic kernel,
uniform stabilizer, normal kernel, theta construction from pairings, the three
low-degree cup pairings, transfer projection formulas, level boundary and cocycle
facts, the prism identities, bilinear and coset averaging, and normal-level
retraction. They are tracked prior child work, not new root helpers. The root
adds no new named helper. The original overlay repeated ten child declarations
and had appended the speculative root body to `transfer_theta`. Integration
retains one existing copy of each child proof and attaches the root body to its
unchanged statement after the dependencies. Warning-fatal checking also required
removing three redundant `letI` bindings in `p08_7d1ff633a4_cp11_level_cocycle`;
the preceding three equivalent `let` bindings remain. Every child statement is
unchanged. This source integration repair preserves the mathematical route and DAG.

The full construction of the transfer and cup operations is the accepted child
work described in Steps 5–17 of the preserved natural proof. The root uses its
proved interface only. In particular, no unresolved geometric statement,
placeholder, new axiom, or historical assertion of review success supplies a
mathematical premise. Lean checking and independent publication review remain
separate from this prose argument.

## Reference use

Exactly one reference source is used: `local-project`, rooted at
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36`.
Its `manifest.json` pins project revision
`9db4b2bea94e42612c675170cfe30ec626166658` and mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`; both reference checkout HEADs and
clean Git status were checked during this round. No network search was used.

Relevant inspected paths relative to that snapshot:

- `project/Definitions/Def_GroupCohomology_Selmer.lean:15–45`: `twist`,
  `dualTwist`, and the dual action formula used in Step 5.
- `project/Definitions/Def_DualSelmer_ExtConditions.lean:13–14`: the exact
  `ofChar` coefficient representation underlying `T`.
- `project/Definitions/Def_GroupCohomology_ContinuousDuality.lean:18–36`:
  the exact representative-based predicates `IsTheta0`, `IsTheta1`, `IsTheta2`.
- `mathlib/Mathlib/RepresentationTheory/Rep/Res.lean:37–56`: restriction
  composes the action and preserves the underlying module.
- `mathlib/Mathlib/LinearAlgebra/Dual/Defs.lean:80–85`: `Module.Dual.eval`
  is evaluation, so its value on `(m,d)` is `d(m)`.
- `mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean:53`:
  `IsUnit.ne_zero`, used to obtain `n ≠ 0` from `hUp`.

Queries included `dualTwist|ofChar`, `eval|theta|Theta`, and the exact
`normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup|corestriction|projection_formula|IsTheta.*exists|exists.*IsTheta`
search in `project/Definitions`. The last search returned no matches. The
`eval|theta|Theta` search in `Def_DualSelmer_ExtConditions.lean` also returned
no matches; its role is the coefficient definition, not a duality lemma.
The homomorphism and inverse identities used in Step 5 are ordinary pinned
mathlib infrastructure. These library facts and definitions are reused with the
configured Lean 4.33.1 elaboration options; compatibility, kernel replay, and
transitive-axiom acceptance are established by validation, not by source
inspection alone.

## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
