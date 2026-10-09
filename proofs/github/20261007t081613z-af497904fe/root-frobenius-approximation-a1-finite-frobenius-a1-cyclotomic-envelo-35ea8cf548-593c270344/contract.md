<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1.inertia_cardinality-a1 -->

## Theorem `Submission.p09_af497904fe_ir_inertia_cardinality`

Let Ω = AlgebraicClosure ℚ and let E be a finite-dimensional Galois intermediate field of Ω/ℚ. Let q be a natural prime, put O = NumberField.RingOfIntegers E, and let P be a prime ideal of O whose contraction to ℤ is (q). Under the canonical action of G = Gal(E/ℚ) on O, let I = {σ ∈ G : σ(a) − a ∈ P for every a ∈ O}. Then Nat.card I = Ideal.ramificationIdx P ℤ.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1.inertia_cardinality-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/690

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_ir_inertia_cardinality`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (q : ℕ), q.Prime → ∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime → P.LiesOver (Ideal.span {(q : ℤ)}) → Nat.card (P.inertia (E ≃ₐ[ℚ] E)) = Ideal.ramificationIdx P ℤ
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1.inertia_cardinality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, q, and P satisfying the hypotheses, and put O = NumberField.RingOfIntegers E, G = Gal(E/ℚ), and p = (q) ⊆ ℤ. Finite-dimensionality gives the number-field structure NumberField.of_module_finite ℚ E. The integer-ring theorems then give that O is a domain, is finite free over ℤ, is integral over ℤ, and has fraction field E. In particular, O is a finite flat ℤ-module. Also G is finite because E/ℚ is finite.
2. Every element of G restricts to an automorphism of O, since it preserves monic polynomial equations with integer coefficients. This is the canonical multiplicative semiring action on O, and it fixes the image of ℤ. The action is faithful: if two automorphisms agree on O, they agree on every fraction a/b with a,b ∈ O and b ≠ 0, hence agree on E.
3. The invariant ring of this action is exactly ℤ. Indeed, if a ∈ O is fixed by every element of G, then its image in E belongs to the fixed field E^G = ℚ, by the Galois fixed-field theorem. This rational element is integral over ℤ. Since ℤ is integrally closed in ℚ, it is an integer. Conversely, every integer is fixed by every rational automorphism. Thus the canonical action satisfies IsGaloisGroup G ℤ O. This is also the integer-ring specialization of IsGaloisGroup.of_isFractionRing.
4. Since q is prime, p is maximal and therefore prime. The quotient ℤ/p is isomorphic to ZMod q, as expressed by Int.quotientSpanNatEquivZMod, and is a finite field. The residue field at the maximal ideal p is this quotient field, hence is perfect. The assumptions on P supply P.IsPrime and P.LiesOver p.
5. Apply Ideal.card_inertia_eq_ramificationIdxIn with R = ℤ, S = O, the canonical group G, the base prime p, and the chosen prime P. Its domain, finite-module, flatness, finite-group, Galois-action, primality, lying-over, and perfect-residue-field hypotheses have all been established in steps 1–4. It yields Nat.card (P.inertia G) = Ideal.ramificationIdxIn p O.
6. Apply Ideal.ramificationIdxIn_eq_ramificationIdx to p, P, and G. The same Galois action and the given lying-over and primality conditions identify Ideal.ramificationIdxIn p O with Ideal.ramificationIdx P ℤ. Substituting this equality into step 5 proves the asserted cardinality formula.

## Key steps

1. Obtain the number-field structure, finite free integer ring, fraction field, and finite automorphism group.
2. Verify that the canonical Galois action preserves integers and is faithful.
3. Identify the invariant ring with ℤ using the Galois fixed field and integral closedness.
4. Identify the residue field at (q) with the perfect finite field ZMod q.
5. Apply Ideal.card_inertia_eq_ramificationIdxIn.
6. Use Ideal.ramificationIdxIn_eq_ramificationIdx to obtain the chosen prime's ramification index.

## Reference use

### local-project

Queries:
- `card_inertia_eq_ramificationIdxIn|ramificationIdxIn_eq_ramificationIdx|inertiaSubgroupIn|def LiesOverPrime`
- `IsGaloisGroup|IsInvariant|FaithfulSMul|MulSemiringAction|IsFractionRing|Module.Free`
- `inertia.*(local|valuation)|ValuationSubring.*inertia|inertia.*ValuationSubring`
- `isDiscreteValuationRing_of_dedekind_domain|valuationSubring|ValuationSubring|ofField|localization`
- `class IsGaloisGroup|of_isFractionRing|IsGaloisGroup.*RingOfIntegers|IsGaloisGroup.*integralClosure`
- `python3 .humanize/ir-split-diagnostic-zj_ybmya/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/RamificationInertia/Galois.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Galois/IsGaloisGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/Int.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/ir-split-diagnostic-zj_ybmya/Types.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/ir-split-diagnostic-zj_ybmya/report.json`

Verified the clean reference snapshots at project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Found the localization-to-DVR theorem, canonical action on rings of integers, ideal inertia definition, valuation residue-action kernel, and both ramification-cardinality formulas. The targeted search found no direct ideal-to-valuation inertia comparison. Both proposed types elaborate after import Submission in a disposable copy of the node's frozen proof base d73bc79fcfa5dc2c71792c1de4c27cc5acae0675. Reflexivity checks confirm that the inferred action on integers is restriction of the field automorphism. NumberField.of_module_finite ℚ E supplies the NumberField instance needed for the finite-module and Galois-group instances. Checked supporting theorem axioms are limited to propext, Classical.choice, and Quot.sound. The diagnostic records policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, exactly omitted lines 10 and 11, reversible original/build hashes, and a successful Lean absence probe for all eight targets. Protected sources and handoffs remained unchanged. These are interface diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
