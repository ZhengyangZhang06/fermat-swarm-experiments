<!-- theorem-id: fermat-p08/root.transfer_theta-a1.transfer_projection-a1.bilinear_averaging-a1 -->

## Theorem `Submission.p08_7d1ff633a4_tp26_bilinear_averaging`

Let k be a field, G a group, X and Y left G-sets, I a finite set, and A,B,N k-representations of G. Let φ : A×B → N be k-bilinear and satisfy φ(ρA(s)a,ρB(s)b)=ρN(s)φ(a,b) for all s,a,b. For any family t : I → G and functions F : X → A and Q : Y → B, the following two conditional identities hold. If F is G-equivariant, then Σ_i ρN(t_i)φ(F(t_i⁻¹·x),Q(t_i⁻¹·y))=φ(F(x),Σ_i ρB(t_i)Q(t_i⁻¹·y)). If Q is G-equivariant, then the same left side equals φ(Σ_i ρA(t_i)F(t_i⁻¹·x),Q(y)). Both identities hold for all x,y; the other function requires no equivariance.

Node: `root.transfer_theta-a1.transfer_projection-a1.bilinear_averaging-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/428

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_tp26_bilinear_averaging`

```lean
∀ {k G X Y ι : Type} [Field k] [Group G] [MulAction G X] [MulAction G Y] [Fintype ι] (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (t : ι → G) (F : X → A) (Q : Y → B), ((∀ (s : G) (x : X), F (s • x) = A.ρ s (F x)) → ∀ (x : X) (y : Y), (∑ c : ι, N.ρ (t c) (φ (F ((t c)⁻¹ • x)) (Q ((t c)⁻¹ • y)))) = φ (F x) (∑ c : ι, B.ρ (t c) (Q ((t c)⁻¹ • y)))) ∧ ((∀ (s : G) (y : Y), Q (s • y) = B.ρ s (Q y)) → ∀ (x : X) (y : Y), (∑ c : ι, N.ρ (t c) (φ (F ((t c)⁻¹ • x)) (Q ((t c)⁻¹ • y)))) = φ (∑ c : ι, A.ρ (t c) (F ((t c)⁻¹ • x))) (Q y))
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

- Parent DAG node: `root.transfer_theta-a1.transfer_projection-a1`
- Child DAG node: `root.transfer_theta-a1.transfer_projection-a1.bilinear_averaging-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix t,F,Q,x,y and an index i. Equivariance of φ rewrites the i-th summand as φ(ρA(t_i)F(t_i⁻¹·x),ρB(t_i)Q(t_i⁻¹·y)). This uses the given equivariance equality in its reverse direction and does not exchange the two arguments.
2. Suppose F is G-equivariant. Applying this equivariance at t_i and t_i⁻¹·x, and using t_i·(t_i⁻¹·x)=x, gives ρA(t_i)F(t_i⁻¹·x)=F(x). Thus each summand from step 1 equals φ(F(x),ρB(t_i)Q(t_i⁻¹·y)).
3. Sum the equalities of step 2. Linearity of b↦φ(F(x),b) moves the finite sum inside the second argument. The result is precisely the first projection identity.
4. Suppose instead Q is G-equivariant. Applying its equivariance at t_i and t_i⁻¹·y gives ρB(t_i)Q(t_i⁻¹·y)=Q(y). The summand in step 1 is therefore φ(ρA(t_i)F(t_i⁻¹·x),Q(y)).
5. Sum these equalities and use additivity in the first argument of φ, equivalently evaluate the sum of linear maps φ(ρA(t_i)F(t_i⁻¹·x)) at Q(y). This yields the second identity. Empty sums are included because both linear maps send zero to zero. All choices were arbitrary, so both conditional identities hold with exactly the stated hypotheses.

## Key steps

1. Use equivariance of φ to move the representation action onto its two inputs.
2. If F is equivariant, cancel its translated input and sum in the second argument.
3. If Q is equivariant, cancel its translated input and sum in the first argument.
4. Keep the order of the two factors throughout.

## Reference use

### local-project

Queries:
- `levelCochains|levelCocycles|levelCoboundaries|continuousH[12]|H1π_eq|cores|transfer|homogeneous`
- `transfer|corestriction|prism|normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup`
- `representative|leftCoset|rightCoset|quotientEquiv|QuotientGroup.mk|exists.*rep|out_eq`
- `index_eq_card|index_eq|def index|card_quotient|FiniteIndex`
- `H1π_eq_zero_iff|H1π_eq_iff|d₀₁_hom_apply|d₁₂_hom_apply|d₂₃_hom_apply`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/GroupTheory/Coset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/GroupTheory/Index.lean`

The snapshot pins project 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. ContinuousH1 defines the carrier as an image of level cocycles; ContinuousH2 uses the quotient by the pulled-back image of level one-cochains. LowDegree supplies the exact H1 representative kernel and equality criteria. Coset/Defs and Coset/Basic supply representative and coset-equality interfaces without requiring H.Normal; Index identifies H.index with Nat.card (G ⧸ H). The focused search of the continuous-cohomology files and mathlib group-cohomology subtree found no transfer, corestriction, prism implementation, or either policy-listed instance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/533

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
