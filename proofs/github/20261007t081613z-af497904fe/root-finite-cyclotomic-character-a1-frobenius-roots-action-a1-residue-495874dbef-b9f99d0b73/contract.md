<!-- theorem-id: fermat-p09/root.finite_cyclotomic_character-a1.frobenius_roots_action-a1.residue_injective-a1 -->

## Theorem `Submission.p09_af497904fe_fcc_fra_residue_injective`

Let Ω = AlgebraicClosure ℚ, let N be a nonzero natural number, let ℓ be a prime natural number with ℓ not dividing N, and let P be a valuation subring of Ω with (ℓ : Ω) ∈ P.nonunits. Write red : P → IsLocalRing.ResidueField P for the residue homomorphism. For any x,y ∈ P satisfying x^N = 1 and y^N = 1 in P, if red(x) = red(y), then x = y in P.

Node: `root.finite_cyclotomic_character-a1.frobenius_roots_action-a1.residue_injective-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/645

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_fcc_fra_residue_injective`

```lean
∀ (N : ℕ) [NeZero N] (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ → ∀ x y : P, x ^ N = 1 → y ^ N = 1 → IsLocalRing.residue P x = IsLocalRing.residue P y → x = y
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

- Parent DAG node: `root.finite_cyclotomic_character-a1.frobenius_roots_action-a1`
- Child DAG node: `root.finite_cyclotomic_character-a1.frobenius_roots_action-a1.residue_injective-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data. Set k = IsLocalRing.ResidueField P and let red : P → k be the residue map. The ring P is a domain because it is a subring of the field Ω, and k is a nontrivial field. Also N ≥ 1.
2. The natural-number element ℓ belongs to P. The hypothesis that its image in Ω lies in P.nonunits says precisely that (ℓ : P) lies in the maximal ideal of P. That ideal is the kernel of red. Consequently red(ℓ) = 0, or equivalently (ℓ : k) = 0.
3. The kernel of the unital homomorphism ℤ → k is exactly ℓℤ. Indeed, step 2 puts every multiple of ℓ in the kernel. If an integer m in the kernel were not divisible by ℓ, primality of ℓ would give gcd(ℓ,m) = 1. Bézout supplies integers a,b with aℓ + bm = 1; applying ℤ → k would yield 0 = 1, a contradiction. Thus k has characteristic ℓ. In particular (N : k) ≠ 0, because otherwise ℓ would divide N, contrary to hypothesis.
4. We first prove that any t ∈ P satisfying t^N = 1 and red(t) = 1 equals 1. If t ≠ 1, form S = ∑_{i=0}^{N−1} t^i in P. Telescoping gives (t−1)S = ∑_{i=0}^{N−1}(t^(i+1)−t^i) = t^N−1 = 0. Since P is a domain and t−1 ≠ 0, this forces S = 0. Applying red gives 0 = ∑_{i=0}^{N−1} red(t)^i = ∑_{i=0}^{N−1} 1 = (N : k), contradicting step 3. Hence t = 1.
5. Now take the x and y in the statement and set v = y^(N−1) in P. Since N ≥ 1, yv = vy = y^N = 1. Also v^N = y^((N−1)N) = (y^N)^(N−1) = 1. This constructs the needed inverse inside P using only its ring operations.
6. Set t = xv. Commutativity gives t^N = x^N v^N = 1. The equal-residue hypothesis and step 5 give red(t) = red(x)red(v) = red(y)red(v) = red(yv) = 1. Step 4 therefore implies xv = 1.
7. Finally x = x(vy) = (xv)y = y. All operations in these steps take place in P, so the conclusion is equality in P, as required. When N = 1 the same identities hold, with v = 1; no separate exclusion is needed.

## Key steps

1. Identify the residue of ℓ as zero using the nonunit hypothesis and the maximal ideal.
2. Use primality and Bézout to show the residue field has characteristic ℓ and the residue of N is nonzero.
3. Use the geometric-sum identity to prove that an N-th root with residue 1 is 1.
4. Construct the inverse of y inside P as y^(N−1).
5. Apply the residue-one result to x y^(N−1), then multiply by y.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|LiesOverPrime|decompositionSubgroup|residueField`
- `pow|IsUnit|isUnit|nonunits|mem_or`
- `rootsOfUnity.*(inject|residue)|(inject|residue).*rootsOfUnity|IsPrimitiveRoot.*(residue|inject)|pow_eq_one.*(residue|mem)|mem.*pow_eq_one`
- `geom_sum_mul|mul_geom_sum|geom_sum_eq`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/CharP/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Ring/GeomSum.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Ideal/Basic.lean`

The manifest pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. LiesOverPrime is exactly ambient membership in P.nonunits. IsFrobeniusAt.smul_residue_eq and IsLocalRing.ResidueField.residue_smul already supply residue-action compatibility. ValuationSubring.mem_or_inv_mem, coe_mem_nonunits_iff, residue_eq_zero_iff, CharP.charP_iff_prime_eq_zero, and geom_sum_mul support the extracted arguments. The search found Ideal.rootsOfUnityMapQuot_injective for number-field integer rings, but no directly applicable reduction-injectivity theorem for the present valuation ring. The consulted infrastructure passed transitive axiom diagnostics with only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/671

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
