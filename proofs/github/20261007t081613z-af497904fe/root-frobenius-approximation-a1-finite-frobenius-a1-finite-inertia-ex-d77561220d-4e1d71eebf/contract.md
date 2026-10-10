<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1.minpoly_roots-a1 -->

## Theorem `Submission.p09_af497904fe_irp_minpoly_roots`

Let E be an intermediate field of AlgebraicClosure ℚ over ℚ, finite-dimensional and Galois over ℚ. For every α ∈ E integral over ℤ, there exist n ∈ ℕ and an injective β : Fin n → E such that every β i is integral over ℤ, every rational automorphic conjugate σ(α) equals some β i, and the coefficient extension of minpoly ℤ α to E equals ∏ i : Fin n, (X − C(β i)).

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1.minpoly_roots-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/710

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_irp_minpoly_roots`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (α : E), IsIntegral ℤ α → ∃ (n : ℕ) (β : Fin n → E), Function.Injective β ∧ (∀ i : Fin n, IsIntegral ℤ (β i)) ∧ (∀ σ : E ≃ₐ[ℚ] E, ∃ i : Fin n, β i = σ α) ∧ (minpoly ℤ α).map (Int.castRingHom E) = Finset.univ.prod (fun i : Fin n => Polynomial.X - Polynomial.C (β i))
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1.minpoly_roots-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, α, and hα : IsIntegral ℤ α. Set f = minpoly ℤ α and g = minpoly ℚ α. The polynomial f is monic and its evaluation at α is zero. Also α is integral over ℚ because E is finite-dimensional over ℚ, so g is monic.
2. By minpoly.isIntegrallyClosed_eq_field_fractions' in Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean, g is the coefficient extension of f from ℤ to ℚ. Composing coefficient maps therefore identifies g extended to E with p = f.map (Int.castRingHom E). Normality, supplied by IsGalois ℚ E, gives that g splits over E by Normal.splits. Separability of E/ℚ gives that g is separable.
3. Apply Polynomial.exists_finset_of_splits from Mathlib/FieldTheory/Separable.lean to g and the rational coefficient map into E. It supplies a finite set s of elements of E such that p = C(g.leadingCoeff mapped to E) · ∏ b ∈ s, (X − C b). Since g is monic, the leading-coefficient factor is 1. Put n = s.card and choose a bijection from Fin n to the subtype of elements of s. Let β be its composition with the subtype inclusion into E. Both maps are injective, so β is injective. Reindexing the finite product gives p = ∏ i : Fin n, (X − C(β i)).
4. For each i, evaluate this factorization at β i. The factor indexed by i becomes zero, so p(β i) = 0. This is precisely the evaluation of the monic integer polynomial f at β i under the integer coefficient map. Thus f witnesses IsIntegral ℤ (β i).
5. Fix a rational algebra automorphism σ of E. Its underlying ring homomorphism fixes every integer. Applying it to the equation f(α) = 0 therefore gives p(σ α) = 0: this follows term by term because σ preserves finite sums, products, powers, and integer coefficients. Evaluating the factorization from step 3 now gives ∏ i : Fin n, (σ α − β i) = 0. In a field a finite product is zero only if one factor is zero. Hence there is i with σ α − β i = 0, equivalently β i = σ α. Together with steps 3 and 4, this proves every asserted conjunct.

## Key steps

1. Identify the integer minimal polynomial after coefficient extension to ℚ and E.
2. Use Galois normality and separability to obtain a finite set of distinct linear factors.
3. Enumerate that set by Fin n and reindex the factorization.
4. Use the monic integer polynomial to prove integrality of every listed root.
5. Apply each automorphism to the vanishing equation and extract a zero linear factor to cover its conjugate.

## Reference use

### local-project

Queries:
- `esymmAlgHom_surjective|coeff_eq_esymm_roots_of_splits|isIntegrallyClosed_eq_field_fractions|prod.*sub.*sq|exists.*discriminant`
- `def IsSymmetric|def esymmAlgHom|esymmAlgHom_X|isSymmetric_iff|def esymm`
- `def esymmAlgHom|theorem.*splits|lemma.*splits|roots.*nodup|nodup.*roots`
- `minpoly|esymm|discriminant|Vandermonde`
- `p09_af497904fe_irp_(minpoly_roots|squared_vandermonde_symmetric|integer_discriminant)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_GaloisRep_Adic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Normal/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Separable.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Polynomial/Vieta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/tmp/p09_irp_decomposition_q9zb6p3m/TypeChecks.lean`
- `/tmp/p09_irp_decomposition_q9zb6p3m/TypeChecks.lean.log`
- `/tmp/p09_irp_decomposition_q9zb6p3m/diagnostic.json`

The manifest pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The snapshot supplies minimal-polynomial coefficient extension, Normal.splits, Polynomial.exists_finset_of_splits, the symmetry predicate, elementary symmetric substitution sending variable i to e_(i+1), and Vieta's coefficient formula. The project definition module search found no relevant polynomial helper. The installed mathlib revision matches and its tracked files are clean. Transitive axiom checks for the six cited library lemmas reported only propext, Classical.choice, and Quot.sound. All three proposed types elaborate after import Submission using the policy-compliant disposable copy; polynomial multiplication instances were inspected. The diagnostic records the matching policy digest, omitted lines, reversible source/build hashes, and successful absence probes for all eight targets. Proposed names have no existing DAG reservation.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/779

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
