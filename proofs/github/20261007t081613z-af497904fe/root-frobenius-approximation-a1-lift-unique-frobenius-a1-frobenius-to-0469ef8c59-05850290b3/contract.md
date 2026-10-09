<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.normal_frobenius_restriction-a1 -->

## Theorem `Submission.p09_af497904fe_ftl_normal_frobenius_restriction`

Let Ω = AlgebraicClosure ℚ. Let E and F be intermediate fields of Ω/ℚ with E ⊆ F and E/ℚ Galois. Write ι : E → F for inclusion. Let V and W be valuation subrings of E and F, respectively, and let ℓ ∈ ℕ. Assume that ι(x) ∈ W if and only if x ∈ V for every x ∈ E. For every rational automorphism g of F satisfying W.IsFrobeniusAt g ℓ, there exists a unique rational automorphism e of E such that V.IsFrobeniusAt e ℓ and ι(e(x)) = g(ι(x)) for every x ∈ E.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.normal_frobenius_restriction-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/661

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_ftl_normal_frobenius_restriction`

```lean
∀ (E F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ E] (hEF : E ≤ F) (V : ValuationSubring E) (W : ValuationSubring F) (ℓ : ℕ), (∀ x : E, IntermediateField.inclusion hEF x ∈ W ↔ x ∈ V) → ∀ g : F ≃ₐ[ℚ] F, W.IsFrobeniusAt g ℓ → ∃! e : E ≃ₐ[ℚ] E, V.IsFrobeniusAt e ℓ ∧ ∀ x : E, IntermediateField.inclusion hEF (e x) = g (IntermediateField.inclusion hEF x)
```

### Frozen project context

`Fermat/Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius.lean` at `20574e45daf714e745af8e649c7b61b21eed5644` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GaloisRep_Adic
attribute [-instance] AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    (hl : IsLocalHom (algebraMap 𝒪 R))
    (ρ : GaloisRepAdic R)
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y] [Module.Finite 𝒪 Y]
    (ρY : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End R Y)
    (hcont : ∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = x) →
        ∀ y : Y, ρY σ y - y ∈ (Ideal.span {(p : R)} ^ n • (⊤ : Submodule R Y)))
    (L : ℕ) [NeZero L] (D : (ZMod L)ˣ →* Module.End R Y)
    (hD : ∀ (u : (ZMod L)ˣ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), D u * ρY σ = ρY σ * D u)
    (S₀ : Finset ℕ)
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ∀ (hℓL : ¬ ℓ ∣ L), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          ρY σ * ρY σ - (ρ.trace σ) • ρY σ
            + (ℓ : R) • D (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)) = 0) :
    ∃ (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ)
      (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ),
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ρY σ * ρY σ - (ρ.trace σ) • ρY σ + ((c σ : Rˣ) : R) • D (χ σ) = 0 := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.normal_frobenius_restriction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data and let ι denote inclusion. Since E/ℚ is Galois, it is algebraic and normal. For x ∈ E, its minimal polynomial over ℚ splits into linear factors over E. Applying g to its vanishing at ι(x) shows that g(ι(x)) is another root, since g fixes rational coefficients. Viewing the factorization in F, one linear factor must vanish at this root. Consequently g(ι(x)) belongs to ι(E). The same argument applies to g⁻¹.
2. Restrict g and g⁻¹ to E using step 1. Injectivity of ι shows that these restrictions preserve addition, multiplication, one and rational scalars, and that their composites are the identity. Thus the restriction e is a rational automorphism of E and satisfies ι(e(x)) = g(ι(x)); its inverse is the restriction of g⁻¹.
3. The Frobenius hypothesis puts g in the decomposition subgroup of W, so g and g⁻¹ preserve W. If x ∈ V, contraction gives ι(x) ∈ W, hence g(ι(x)) ∈ W, hence e(x) ∈ V. Applying the same argument to the inverses shows that e⁻¹ preserves V. Therefore e maps V onto itself and belongs to V.decompositionSubgroup ℚ.
4. For every x ∈ E, nonunits contract exactly: ι(x) ∈ W.nonunits if and only if x ∈ V.nonunits. Indeed, ValuationSubring.mem_nonunits_iff_or expresses the first assertion as ι(x) = 0 or ι(x)⁻¹ ∉ W. Inclusion is injective, preserves zero and inverses, and contracts W to V. This assertion is therefore equivalent to x = 0 or x⁻¹ ∉ V, which is precisely the second assertion.
5. Take x ∈ V. In the residue field of W, the Frobenius property of g gives [g(ι(x))] = [ι(x)]^ℓ. The residue map is a ring homomorphism with kernel the maximal ideal, whose image in F is W.nonunits. Hence g(ι(x)) − ι(x)^ℓ belongs to W.nonunits. This difference equals ι(e(x) − x^ℓ). Step 4 implies e(x) − x^ℓ ∈ V.nonunits. Passing to the residue field of V gives [e(x)] = [x]^ℓ. Every residue class has a representative in V, and the decomposition-group action on its residue is the residue of e(x). Together with step 3 this proves V.IsFrobeniusAt e ℓ.
6. If e′ is another rational automorphism satisfying the asserted conjunction, its commuting equation gives ι(e′(x)) = g(ι(x)) = ι(e(x)) for every x ∈ E. Injectivity of ι yields e′(x) = e(x) for all x, so e′ = e. This proves existence and uniqueness.

## Key steps

1. Use normality and split minimal polynomials to restrict g and g⁻¹ to E.
2. Use contraction of valuation rings to show the restricted automorphism stabilizes V.
3. Contract nonunits using the zero-or-inverse criterion.
4. Descend the Frobenius residue equation through nonunit contraction.
5. Prove uniqueness by injectivity of the field inclusion.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|mem_nonunits_iff_or|exists.*compatible|inverse.*limit|restrictNormal|LiesOverPrime`
- `def IsFrobeniusAt|def LiesOverPrime|def decompositionSubgroup|theorem.*IsFrobeniusAt`
- `glue|iSup|directLimit|exists.*equiv`
- `maximalIdeal|nonunits|residue.*smul|smul.*residue`
- `p09_af497904fe_ftl_(normal_frobenius_restriction|compatible_automorphisms_glue|frobenius_valuation_union)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Normal/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/CategoryTheory/CofilteredSystem.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-finite-inverse-limit-a1/integration-lean-audit-v1.json`
- `/runtime/review-evidence/5190b66052c64f30b33294a3056dcb3f/evidence.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p09_tower_decomposition_eui_c1e8/TypesAfterSubmission.lean`
- `/tmp/p09_tower_decomposition_eui_c1e8/record.json`

The snapshot pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected definitions identify LiesOverPrime with ambient nonunit membership and IsFrobeniusAt with decomposition-group membership plus the residue power action. ValuationSubring.mem_nonunits_iff_or and coe_mem_nonunits_iff justify nonunit contraction; residue_eq_zero_iff and residue_smul justify passing between residue equations and differences in nonunits. Normal/Defs supplies normal restriction and its commuting equation. The IntermediateField search found directed-union infrastructure but no directly applicable automorphism-gluing theorem. The inherited p09_af497904fe_finite_inverse_limit already has exact-comparator and permitted-axiom evidence, so no duplicate node is proposed. Proposed names have no matches in the inspected DAG or Submission. All three exact types compiled after literal import Submission using a disposable copy of frozen base 3915a640f981289a567a646ed42a4a5f880b9d24; their axiom reports contain only propext, Classical.choice and Quot.sound. Policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 was checked, only original lines 10 and 11 were omitted, and Lean verified all eight omitted targets absent. Original sources remained unchanged. These are interface diagnostics, not proof acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
