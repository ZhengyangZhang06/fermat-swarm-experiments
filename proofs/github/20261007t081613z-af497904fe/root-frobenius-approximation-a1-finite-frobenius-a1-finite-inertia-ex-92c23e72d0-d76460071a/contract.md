<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.valuation_product_separation-a1 -->

## Theorem `Submission.p09_af497904fe_cs_valuation_product_separation`

Let K be a field, n ∈ ℕ, β : Fin n → K, and D ∈ ℤ. Suppose every β i is integral over ℤ and the image of D in K equals ∏_{i<j}(β i − β j)². For every natural prime ℓ not dividing D.natAbs and every valuation subring V of K satisfying V.LiesOverPrime ℓ, every β i belongs to V, and β i − β j ∈ V.nonunits implies β i = β j for all i,j. Here V.LiesOverPrime ℓ means (ℓ : K) ∈ V.nonunits, and V.nonunits is the subset of K obtained from the nonunits of V. No characteristic-zero, injectivity, or separate nonzero-D hypothesis is required.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.valuation_product_separation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/695

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_cs_valuation_product_separation`

```lean
∀ {K : Type} [Field K] (n : ℕ) (β : Fin n → K) (D : ℤ), (∀ i : Fin n, IsIntegral ℤ (β i)) → (D : K) = (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod (fun ij => (β ij.1 - β ij.2) ^ 2) → ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ D.natAbs → ∀ V : ValuationSubring K, V.LiesOverPrime ℓ → (∀ i : Fin n, β i ∈ V) ∧ ∀ i j : Fin n, β i - β j ∈ V.nonunits → β i = β j
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.valuation_product_separation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, n, β, D, the integrality and product hypotheses, and an allowed prime ℓ and valuation subring V. Let m be the maximal ideal of the local ring V. Every integer cast belongs to V because V is a subring. For an element of V, its image in K belongs to V.nonunits exactly when that element belongs to m; this is ValuationSubring.coe_mem_nonunits_iff.
2. We first prove that every x ∈ K integral over ℤ belongs to V. Suppose instead that x ∉ V. Since 0 ∈ V, x ≠ 0. The valuation-subring property gives t = x⁻¹ ∈ V. The element t is not a unit of V: a V-inverse s would satisfy ts = 1 in K, forcing s = x and hence x ∈ V. Thus t ∈ m.
3. Choose a monic integer polynomial witnessing integrality of x, and write its equation as x^r + ∑_{k<r} a_k x^k = 0. Its degree r is positive, because a monic degree-zero polynomial is 1 and cannot vanish in a field. Multiply the equation in K by x^(−r), obtaining 1 + ∑_{k<r} a_k t^(r−k) = 0. All terms now belong to V, so injectivity of V → K makes this an equality in V. Each exponent r−k is positive, so t ∈ m implies t^(r−k) ∈ m. Multiplication by the integer coefficient preserves membership in m, as do finite sums and negation. The equation therefore implies 1 ∈ m, contradicting properness of m. This proves the containment claim, and applying it to each β i gives the first conclusion.
4. Since ℓ is prime and does not divide D.natAbs, the integers D and ℓ are relatively prime. Indeed, the positive gcd of D.natAbs and ℓ divides the prime ℓ, so it is either 1 or ℓ; the latter is excluded by nondivisibility. Integer Bézout gives u,v ∈ ℤ with uD + vℓ = 1. The hypothesis V.LiesOverPrime ℓ and step 1 put the element (ℓ : V) in m. If (D : V) also belonged to m, the Bézout identity, mapped into V, would put 1 in m. Hence (D : V) is outside m and is a unit of V.
5. Lift every β i to b_i ∈ V using step 3. The inclusion V → K preserves integer casts, subtraction, powers, and finite products. Its injectivity therefore lifts the assumed product equality to (D : V) = ∏_{i<j}(b_i − b_j)² in V. Every factor in this product belongs to V.
6. Fix i,j and suppose β i − β j ∈ V.nonunits. If i = j, the desired equality follows immediately. Otherwise, let a be the smaller of i,j and b the larger. By step 1, b_i − b_j belongs to m. The ordered difference b_a − b_b is either this element or its negative, so its square belongs to m. The pair (a,b) occurs in the filtered product of step 5. Factoring out its squared difference expresses that product as an element of m times a product of elements of V; ideal closure puts the whole product in m. This says (D : V) ∈ m, contradicting step 4. The unequal-index case is impossible, and therefore β i = β j. Together with step 3 this proves both conclusions for the arbitrary permitted ℓ and V, hence uniformly for all of them.

## Key steps

1. Identify ambient valuation nonunits with membership in the maximal ideal of V.
2. For an integral element outside V, put its inverse in the maximal ideal.
3. Divide a monic integral equation by its leading power to derive the contradiction 1 ∈ m.
4. Apply integer Bézout and LiesOverPrime to show that D is a unit of V.
5. Lift the integer product equality from K to V.
6. A nonunit difference at unequal indices forces a squared factor, and thus D, into the maximal ideal.

## Reference use

### local-project

Queries:
- `rg -n --glob '*.lean' 'LiesOverPrime|esymmAlgHom_surjective|isIntegrallyClosed_eq_field_fractions\x27|mem_of_isIntegral|isIntegral.*mem' project mathlib/Mathlib/RingTheory/Valuation mathlib/Mathlib/RingTheory/IntegralClosure mathlib/Mathlib/RingTheory/MvPolynomial mathlib/Mathlib/FieldTheory/Minpoly`
- `rg -n 'esymm.*coeff|coeff.*esymm|vieta' mathlib/Mathlib -g '*.lean'`
- `rg -n 'nodup_roots|separable_map|theorem separable|minpoly.*separable' mathlib/Mathlib/FieldTheory/Separable.lean mathlib/Mathlib/FieldTheory/Perfect.lean`
- `rg -n --glob '*.lean' 'integer_root_product|valuation_product_separation|conjugate_separation' project/Definitions project/Theorems project/Submission.lean`
- `sed -n '551,626p' mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `python3 .humanize/cs-split-diagnostic-p625iw0i/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Separable.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Polynomial/Vieta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/cs-split-diagnostic-p625iw0i/report.json`

Search commands using project/ and mathlib/ were run from the specified snapshot root. The snapshot confirms the minimal-polynomial compatibility theorem, separability and distinct-root APIs, MvPolynomial.esymmAlgHom_surjective with generators indexed by i+1, Vieta identities, and the bridge from ambient valuation nonunits to the maximal ideal. LiesOverPrime is exactly membership of the natural-number cast in ambient nonunits. The proposed-helper-name search returned no matches in the searched pinned project files. Project revision 20574e45daf714e745af8e649c7b61b21eed5644, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and pinned dependencies were checked clean. Both proposed types elaborated after import Submission at proof-base commit 0e4c21ecef38655f90fdf89c00e55ba35d7e9369 using a disposable policy-compliant compiler copy. Integer casts, valuation-subring multiplication, and the ambient-nonunit interpretation were checked. Audited library declarations depend only on propext, Classical.choice, and Quot.sound. The diagnostic receipt records the matching policy digest, exact omitted lines 10 and 11, reversible original/build hashes, and a successful Lean absence probe for all eight omitted targets. Protected files remained unchanged. These are interface diagnostics, not comparator proof acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/767

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
