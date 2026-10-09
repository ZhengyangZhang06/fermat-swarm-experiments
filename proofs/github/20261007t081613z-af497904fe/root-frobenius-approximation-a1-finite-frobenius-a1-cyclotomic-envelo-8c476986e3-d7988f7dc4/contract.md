<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.compositum_pair-a1 -->

## Theorem `Submission.p09_af497904fe_ce_compositum_pair`

Let Ω = AlgebraicClosure ℚ. Let E and C be finite-dimensional Galois intermediate fields of Ω/ℚ with E ∩ C = ℚ. For every g ∈ Gal(E/ℚ) and a ∈ Gal(C/ℚ), there exists a unique rational automorphism h of M = E ⊔ C such that h ∘ ι_E = ι_E ∘ g and h ∘ ι_C = ι_C ∘ a, where ι_E and ι_C are the canonical inclusions into M.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.compositum_pair-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/679

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_ce_compositum_pair`

```lean
∀ (E C : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] [FiniteDimensional ℚ C] [IsGalois ℚ C], E ⊓ C = ⊥ → ∀ (g : E ≃ₐ[ℚ] E) (a : C ≃ₐ[ℚ] C), ∃! h : ↥(E ⊔ C) ≃ₐ[ℚ] ↥(E ⊔ C), (∀ x : E, h (IntermediateField.inclusion (show E ≤ E ⊔ C from le_sup_left) x) = IntermediateField.inclusion (show E ≤ E ⊔ C from le_sup_left) (g x)) ∧ (∀ y : C, h (IntermediateField.inclusion (show C ≤ E ⊔ C from le_sup_right) y) = IntermediateField.inclusion (show C ≤ E ⊔ C from le_sup_right) (a y))
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.compositum_pair-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, C, g, and a, and put M = EC inside Ω. The products of elements from finite rational bases of E and C span a finite-dimensional subalgebra containing both fields. A finite-dimensional domain over a field is a field, so this subalgebra is M and M is finite-dimensional. Both E and C are splitting fields of separable polynomials over ℚ; the union of these sets of roots generates M. Thus M/ℚ is normal and separable, hence Galois. Also M/C is finite Galois.
2. Restriction defines a homomorphism r : Gal(M/C) → Gal(E/ℚ). It is well-defined because E/ℚ is normal. It is injective: an element in its kernel fixes E and C, and therefore fixes the field they generate, namely M.
3. Write J for the image of r. An element x of E is fixed by J exactly when it is fixed by every element of Gal(M/C). By finite Galois correspondence for M/C, this is equivalent to x belonging to C. Thus the fixed field E^J is E ∩ C = ℚ. Finite Galois correspondence for E/ℚ now gives J = Gal(E/ℚ). Hence r is bijective, and [M:C] = |Gal(M/C)| = |Gal(E/ℚ)| = [E:ℚ].
4. Simultaneous restriction gives R : Gal(M/ℚ) → Gal(E/ℚ) × Gal(C/ℚ). Both restrictions are well-defined by normality. If two automorphisms have the same restrictions, their equalizer is an intermediate field containing E and C, so it is M; therefore R is injective. The degree formula and step 3 give |Gal(M/ℚ)| = [M:ℚ] = [M:C][C:ℚ] = [E:ℚ][C:ℚ], equal to the cardinality of the product target. Consequently R is bijective.
5. Let h be the unique inverse image under R of (g,a). The two coordinates of R(h) = (g,a), expressed through the canonical inclusions of E and C into M, are exactly the two families of equations in the statement. Injectivity of R proves uniqueness.

## Key steps

1. Show the compositum is finite Galois over ℚ and Galois over C.
2. Restrict Gal(M/C) injectively to Gal(E/ℚ).
3. Identify the fixed field of the restriction image with E ∩ C and conclude surjectivity.
4. Use the resulting degree equality to make simultaneous restriction bijective.
5. Take the unique inverse image of the prescribed pair.

## Reference use

### local-project

Queries:
- `inertiaSubgroupIn|LiesOverPrime`
- `card.*inertia|inertia.*card|ramificationIdx.*eq|equiv.*inertia`
- `ramificationIdx_tower`
- `isDiscreteValuationRing_of_dedekind_domain`
- `exists_ideal_over_prime_of_isIntegral_of_isDomain`
- `restrict.*(Equiv|equiv)|inf_eq_bot|linearDisjoint|sup.*finrank|fixedField.*fixing|fixing.*fixedField`
- `Gal.*×.*Gal|≃\*.*×|prod.*restrictNormal|restrictNormal.*prod|exists.*algEquiv.*(sup|compositum)|exists.*prime.*(one|modEq)`
- `rg -n 'theorem|lemma' Mathlib/NumberTheory/LSeries/PrimesInAP.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/Gal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/LSeries/PrimesInAP.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/RamificationInertia/Galois.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RamificationInertia/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RamificationInertia/Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/GoingUp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Galois/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Normal/Basic.lean`

Confirmed clean snapshots at project revision 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. LiesOverPrime means that the rational prime is a nonunit; inertiaSubgroupIn is the image of the residue-action kernel in the rational automorphism group. Found Ideal.card_inertia_eq_ramificationIdxIn, Ideal.ramificationIdxIn_eq_ramificationIdx, the ramification tower and degree formulas, prime lifting, prime-cyclotomic total ramification, restriction-map injectivity and surjectivity, and finite Galois correspondence. Nat.forall_exists_prime_gt_and_modEq and IsCyclotomicExtension.autEquivPow cover the prime-choice and cyclotomic-group infrastructure. The searched FieldTheory modules did not provide the exact unique paired-restriction interface proposed below. Supporting declarations audited by the diagnostic depend only on propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
