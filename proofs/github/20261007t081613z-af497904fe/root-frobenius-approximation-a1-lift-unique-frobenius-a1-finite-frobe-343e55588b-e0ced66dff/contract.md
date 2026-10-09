<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1.localized_frobenius-a1 -->

## Theorem `Submission.p09_af497904fe_ffe_localized_frobenius`

Let Ω = AlgebraicClosure ℚ, let E be any intermediate field of Ω/ℚ, and let ℓ be a natural prime. Write O = NumberField.RingOfIntegers E. Let V be a valuation subring of E and q a prime ideal of O. Assume that, for every x ∈ E, x ∈ V if and only if x = a/b for some a,b ∈ O with b ∉ q. Assume also that, for every a ∈ O, its image in E belongs to V.nonunits if and only if a ∈ q. If g ∈ Autℚ(E) satisfies γg(a) − a^ℓ ∈ q for every a ∈ O, where γg is its restriction to O, then V.IsFrobeniusAt g ℓ.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1.localized_frobenius-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/660

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_ffe_localized_frobenius`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (ℓ : ℕ), ℓ.Prime → ∀ (V : ValuationSubring E) (q : Ideal (NumberField.RingOfIntegers E)), q.IsPrime → (∀ x : E, x ∈ V ↔ ∃ a b : NumberField.RingOfIntegers E, b ∉ q ∧ x = (a : E) / (b : E)) → (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V.nonunits ↔ a ∈ q) → ∀ g : E ≃ₐ[ℚ] E, (∀ a : NumberField.RingOfIntegers E, NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv a - a ^ ℓ ∈ q) → V.IsFrobeniusAt g ℓ
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

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1.localized_frobenius-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data and hypotheses, and write γ for NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv. This is a ring automorphism of O whose value on a, viewed in E, is g(a). Its inverse is the restriction of g⁻¹. Since q is prime, it is proper, so 1 ∉ q. The fraction characterization applied to a/1 shows that every a ∈ O belongs to V. Thus inclusion defines a ring homomorphism i : O → V.
2. The congruence hypothesis gives γ(a) − a^ℓ ∈ q. Consequently γ(a) ∈ q if and only if a^ℓ ∈ q, by closure of q under addition and subtraction. Since ℓ > 0 and q is prime, a^ℓ ∈ q if and only if a ∈ q: one direction follows from ideal closure and the other from repeated application of primality to the product a^ℓ. Therefore γ(a) ∈ q if and only if a ∈ q. Applying this equivalence to γ⁻¹(a) shows that γ⁻¹ also preserves q and its complement.
3. If x ∈ V, write x = a/b with a,b ∈ O and b ∉ q using the fraction hypothesis. The equality g(x) = γ(a)/γ(b), together with γ(b) ∉ q, shows that g(x) ∈ V. The same argument using γ⁻¹ shows that g⁻¹ maps V into V. Hence g maps V onto itself. The decomposition subgroup is the stabilizer of V under the field-automorphism action, so this supplies hg : g ∈ V.decompositionSubgroup ℚ.
4. Let K_V = IsLocalRing.ResidueField V, let r : V → K_V be reduction, and put κ = r ∘ i : O → K_V. For any a ∈ O, κ(a) = 0 if and only if i(a) belongs to the maximal ideal of V. For a valuation ring this is equivalent to the image of a in E belonging to V.nonunits, which by hypothesis is equivalent to a ∈ q. Thus ker κ = q. In particular, b ∉ q implies κ(b) ≠ 0. Applying κ to the congruence hypothesis now gives κ(γ(a)) = κ(a)^ℓ for every a ∈ O.
5. Take any v ∈ V and write its image in E as a/b with b ∉ q. Since 0 ∈ q, b is nonzero in O, and hence in E. Multiplication of the fraction equality by b gives v · i(b) = i(a) in V. Reducing this equality gives r(v)κ(b) = κ(a). Since κ(b) ≠ 0, it follows that r(v) = κ(a)/κ(b).
6. The automorphism of V induced by hg sends v to an element whose image in E is γ(a)/γ(b). We have γ(b) ∉ q by step 2. Applying the calculation of step 5 to this fraction gives r(g(v)) = κ(γ(a))/κ(γ(b)). By step 4 this equals κ(a)^ℓ/κ(b)^ℓ = (κ(a)/κ(b))^ℓ = r(v)^ℓ. Here g(v) denotes the restriction of g to V; its existence was established in step 3.
7. The induced residue action satisfies (⟨g,hg⟩ : V.decompositionSubgroup ℚ) • r(v) = r(g(v)). This is exactly the action defined in Mathlib/RingTheory/Valuation/RamificationGroup.lean and Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean, where residue_smul expresses compatibility with reduction. Every element z of K_V is r(v) for some v, because the residue map is surjective. Step 6 therefore gives (⟨g,hg⟩ : V.decompositionSubgroup ℚ) • z = z^ℓ for every z ∈ K_V.
8. The witness hg from step 3 and the equality from step 7 satisfy precisely the definition of V.IsFrobeniusAt g ℓ in the pinned Definitions/Def_EllipticCurve_FrobeniusTrace.lean. This proves the conclusion.

## Key steps

1. Embed O into V using fractions with denominator 1.
2. Use the congruence and primality to prove that γ and γ⁻¹ preserve q and its complement.
3. Use the fraction description to prove that g stabilizes V.
4. Identify the kernel of O → ResidueField V with q and reduce the integer congruences.
5. Compute residues of a/b and g(a/b), obtaining the ℓ-power equality.
6. Use surjectivity of reduction and the canonical residue action to establish IsFrobeniusAt.

## Reference use

### local-project

Queries:
- `valuation_localization|stabilizerHom_surjective|mem_range_algebraMap_iff_fixed|def IsFrobeniusAt|def decompositionSubgroup`
- `RingOfIntegers|map|equiv|smul|IsInvariant`
- `ResidueField|residue|smul|nonunits`
- `rg -n '"lean_name"|"status"|"proof_worktree"|"worktree"' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/usr/bin/python3 .humanize/ffe-split-diagnostic-lnp4jtq3/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Galois/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Invariant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Invariant/Galois.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Frobenius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/ffe-split-diagnostic-lnp4jtq3/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/ffe-split-diagnostic-lnp4jtq3/types.json`

The snapshot pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. It supplies the integer-ring restriction map, fixed-field criterion, stabilizer-surjectivity theorem, and exact decomposition-group residue action. No valuation_localization declaration was found in the snapshot; the active DAG already reserves that obligation as p09_af497904fe_luf_valuation_localization. Both proposed types elaborated after literal import Submission in a disposable compiler copy, and neither proposed name collided with the inspected DAG or imported environment. Definitional checks confirmed that mapRingEquiv restricts the field automorphism and agrees with the canonical integer-ring action. The types and checked library results have only propext, Classical.choice, and Quot.sound as transitive axioms. Diagnostics verified the specified policy digest, absence of all eight omitted targets, reversible removal of exactly lines 10 and 11, and preservation of protected sources and handoffs. These are interface diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
