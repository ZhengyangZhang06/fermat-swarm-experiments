<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1 -->

## Theorem `Submission.p09_af497904fe_ce_cyclotomic_intersection`

Let Ω = AlgebraicClosure ℚ, let E be a finite-dimensional Galois intermediate field of Ω/ℚ, let q be a natural prime, and let ζ ∈ Ω be a primitive qth root of unity. Assume that every valuation subring V of E in which q is a nonunit has trivial rational inertia subgroup. Then E ∩ ℚ(ζ) = ℚ, equivalently E ⊓ IntermediateField.adjoin ℚ {ζ} = ⊥.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/679

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/690

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/713, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/714

## Lean problem

Declaration: `Submission.p09_af497904fe_ce_cyclotomic_intersection`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (q : ℕ) (ζ : AlgebraicClosure ℚ), q.Prime → IsPrimitiveRoot ζ q → (∀ V : ValuationSubring E, V.LiesOverPrime q → ∀ τ : E ≃ₐ[ℚ] E, τ ∈ V.inertiaSubgroupIn ℚ → τ = 1) → E ⊓ IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) = ⊥
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
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data and put C = ℚ(ζ). Apply inertia_ramification to E and q. It follows that every prime of the ring of integers of E above q has ramification index one.
2. The polynomial Φ_q(X) = 1 + X + ⋯ + X^(q−1) vanishes at ζ. Its translate Φ_q(X+1) is monic, has constant coefficient q, and all other nonleading coefficients are divisible by q, by the binomial coefficients of (X+1)^q. It is irreducible by Eisenstein: Gauss's lemma would turn a proper rational factorization into monic integer factors; reduction modulo q would make both nonconstant factors powers of X, forcing both constant coefficients to be divisible by q, whereas their product is q. Thus [C:ℚ] = q−1. Its conjugates are the distinct ζ^i for 1 ≤ i < q, all lying in C, so C/ℚ is finite Galois.
3. The element ζ is integral, and N_{C/ℚ}(1−ζ) = ∏_{i=1}^{q−1}(1−ζ^i) = Φ_q(1) = q. For each i in that range, u_i = (1−ζ^i)/(1−ζ) = 1 + ζ + ⋯ + ζ^(i−1) is integral. The numerator is a conjugate of the denominator, so N(u_i) = 1. Multiplication by u_i on an integral basis has an integer matrix of determinant one. Its adjugate gives an integer inverse matrix; applying this inverse to 1 shows u_i^(-1) is integral. Hence each u_i is a unit of O_C.
4. Put A = (1−ζ)O_C. The norm-index formula for principal ideals gives |O_C/A| = q, so A is maximal with residue field 𝔽_q. Multiplying the identities 1−ζ^i = u_i(1−ζ) gives qO_C = A^(q−1). Every prime above q therefore contains A and equals A. Thus C has exactly one prime above q, with residue degree one. These conclusions also hold for q = 2; no odd-prime assumption was used.
5. Let D = E ∩ C and let R be the contraction of A to O_D. Every prime of O_D above q lifts to a prime of O_C, because O_C is integral over O_D. Step 4 forces every such lifted prime to be A, so R is the unique prime of D above q. The injection O_D/R → O_C/A identifies O_D/R with a subfield of 𝔽_q containing its prime field 𝔽_q. Consequently its residue degree over q is one.
6. Apply the number-field degree formula ∑ e f = [D:ℚ], formalized by the ramification-inertia degree theorem. There is only the prime R in this sum and its residue degree is one, so e(R/q) = [D:ℚ]. The formula applies to D without a Galois assumption: D is finite over ℚ, and its ring of integers is finite free over ℤ.
7. Lift R to a prime P of O_E using integrality of O_E over O_D. Ramification indices multiply in this tower, so e(P/q) = e(P/R)e(R/q). The left side is one by step 1. Both factors are positive integers for primes in finite number-field extensions; hence e(R/q) = 1.
8. Steps 6 and 7 give [D:ℚ] = 1. The rational subfield of D already has dimension one, so it is all of D. Therefore D is the bottom intermediate field of Ω/ℚ, proving the stated intersection equality.

## Key steps

1. Use inertia_ramification to obtain ramification index one throughout E above q.
2. Establish the degree and conjugates of the prime-cyclotomic field by Eisenstein.
3. Use norms and cyclotomic units to prove qO_C = ((1−ζ)O_C)^(q−1).
4. Show every intermediate field of C has one prime above q with residue degree one.
5. Apply the degree formula to D = E ∩ C.
6. Use prime lifting and multiplicativity through E to force [D:ℚ] = 1.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/794

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
