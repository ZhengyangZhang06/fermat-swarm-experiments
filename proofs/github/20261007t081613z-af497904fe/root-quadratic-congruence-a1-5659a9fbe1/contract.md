<!-- theorem-id: fermat-p09/root.quadratic_congruence-a1 -->

## Theorem `Submission.p09_af497904fe_quadratic_congruence`

Let C be a commutative ring, M an additive commutative group with a C-module structure, J an ideal of C, a,b,d ∈ End_C(M), and s,r,u,v ∈ C. Suppose (a−b)y ∈ J • ⊤ for every y, s−r ∈ J and u−v ∈ J. Then ((a*a−s•a+u•d)−(b*b−r•b+v•d))y ∈ J • ⊤ for every y. Multiplication is composition of endomorphisms; no commutation hypothesis on a,b,d is imposed.

Node: `root.quadratic_congruence-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_quadratic_congruence`

```lean
∀ {C M : Type} [CommRing C] [AddCommGroup M] [Module C M] (J : Ideal C) (a b d : Module.End C M) (s r u v : C), (∀ y : M, (a - b) y ∈ J • (⊤ : Submodule C M)) → s - r ∈ J → u - v ∈ J → ∀ y : M, ((a * a - s • a + u • d) - (b * b - r • b + v • d)) y ∈ J • (⊤ : Submodule C M)
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

- Parent DAG node: `root`
- Child DAG node: `root.quadratic_congruence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let N = J • (⊤ : Submodule C M). Every C-linear endomorphism preserves N, since it maps a finite sum of terms α • z with α ∈ J to the corresponding sum with the same scalar coefficients. Also α • z ∈ N whenever α ∈ J and z ∈ M.
2. Distributivity and the scalar rules give the ordered identity (a*a−s•a+u•d)−(b*b−r•b+v•d) = a*(a−b)+(a−b)*b−s•(a−b)−(s−r)•b+(u−v)•d. Expanding the first two terms cancels −a*b with +a*b; expanding the next two cancels +s•b with −s•b. No endomorphism factors are interchanged.
3. Fix y ∈ M. The first term evaluates to a((a−b)y), which lies in N by the image hypothesis and preservation of N. The second evaluates to (a−b)(b(y)), which lies in N by the same hypothesis applied to b(y). The third evaluates to −s • ((a−b)y), which lies in N by submodule closure under scalars and negation.
4. The fourth term evaluates to −(s−r) • b(y), and the fifth to (u−v) • d(y). They lie in N because their scalar coefficients belong to J, using ideal closure under negation for the fourth.
5. Closure under sums and the identity in step 2 show that the entire required difference evaluated at y belongs to N. Since y was arbitrary, this proves the conclusion.

## Key steps

1. Show that linear endomorphisms preserve ideal multiples.
2. Expand the quadratic difference without commuting factors.
3. Control the three terms involving a−b.
4. Control the two terms with scalar coefficients in J.
5. Combine the memberships by submodule closure.

## Reference use

### local-project

Queries:
- `rg -n 'modularCyclotomicCharacter|theorem spec|theorem unique|TODO|IsAdicComplete|exists_pow_inf_eq_pow_smul|iInf_pow_smul_eq_bot_of_isLocalRing|trace_eq_matrix_trace' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Filtration.lean .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `rg -n 'Chebotarev|chebotarev|FrobeniusDensity' project/Definitions mathlib/Mathlib/NumberTheory mathlib/Mathlib/RingTheory`
- `rg -n 'smul_eq_mul|theorem sub_apply|theorem smul_apply' mathlib/Mathlib/Algebra/Algebra/Operations.lean mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean`
- `python3 .humanize/decomposition-interface-fresh-tdjulkl6/finish.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_GaloisRep_Adic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Filtration.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Algebra/Operations.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Module/LinearMap/End.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Frobenius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/Complex/Polynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/decomposition-interface-fresh-tdjulkl6/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/decomposition-interface-fresh-tdjulkl6/name-reservations.json`

The snapshot matches project commit 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d; both tracked trees are clean. Relative search paths above use the stated snapshot root. The definitions confirm the exact continuity, trace, LiesOverPrime and arithmetic IsFrobeniusAt predicates. Mathlib supplies finite cyclotomic characters, adic completeness, Artin–Rees, finite-module separation and matrix trace identification; cyclotomic compatibility is explicitly a TODO and is proved below. The Chebotarev/FrobeniusDensity search returned no matches in its three searched subtrees. RingTheory/Frobenius.lean supplies Frobenius at a given prime, not the required prime-distribution assertion. Fresh disposable checks passed for all eight unchanged types after both import Submission and import Challenge, including composition, pointwise linear-map operations and ideal-action probes. Inspected type and supporting-declaration axiom dependencies are subsets of propext, Classical.choice and Quot.sound. The report records the exact policy-authorized omissions, a successful eight-target absence probe, original/build hashes and unchanged protected files. These are interface diagnostics, not comparator acceptance or accepted child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
