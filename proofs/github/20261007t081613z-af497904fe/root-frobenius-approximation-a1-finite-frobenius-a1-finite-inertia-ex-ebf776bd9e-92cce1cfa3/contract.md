<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1 -->

## Theorem `Submission.p09_af497904fe_cs_integer_root_product`

Let E be an intermediate field of AlgebraicClosure ℚ over ℚ, with E finite-dimensional and Galois over ℚ. Let α ∈ E be integral over ℤ. There exist n ∈ ℕ, an injective family β : Fin n → E, and D ∈ ℤ such that every β i is integral over ℤ, every ℚ-automorphic conjugate σ(α) equals some β i, D ≠ 0, and the image of D in E equals the product of (β i − β j)² over all pairs i < j in Fin n.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/695

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/731, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/732, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/733

## Lean problem

Declaration: `Submission.p09_af497904fe_cs_integer_root_product`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (α : E), IsIntegral ℤ α → ∃ (n : ℕ) (β : Fin n → E) (D : ℤ), Function.Injective β ∧ (∀ i : Fin n, IsIntegral ℤ (β i)) ∧ (∀ σ : E ≃ₐ[ℚ] E, ∃ i : Fin n, β i = σ α) ∧ D ≠ 0 ∧ (D : E) = (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod (fun ij => (β ij.1 - β ij.2) ^ 2)
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
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, α, and the asserted integrality of α. Put f = minpoly ℤ α and g = minpoly ℚ α. Integrality makes f monic and gives f(α) = 0. The theorem minpoly.isIntegrallyClosed_eq_field_fractions' identifies g with f after coefficient extension from ℤ to ℚ. Thus their further coefficient extensions to E agree; write this polynomial as f_E. Its degree n is positive: a monic polynomial of degree zero is 1 and cannot vanish at α in the field E.
2. Normality of E/ℚ makes g split over E. Separability of E/ℚ makes g separable, and coefficient extension preserves separability. Consequently f_E splits into n distinct linear factors. Enumerate its roots without repetition by β : Fin n → E. Then β is injective and f_E = ∏ i : Fin n, (X − C(β i)). This enumeration exists because a split nonzero polynomial has as many roots counted with multiplicity as its degree, while separability makes that root multiset have no repetitions.
3. Each β i satisfies the monic integer polynomial f, so IsIntegral ℤ (β i). For a rational automorphism σ of E, applying σ to f(α) = 0 gives f(σ(α)) = 0: σ preserves addition and multiplication and fixes every integer coefficient. Therefore σ(α) is a root of f_E and equals β i for some i. This proves the integrality and conjugate-coverage assertions.
4. In the polynomial ring with variables X_i indexed by Fin n and coefficients in ℤ, define P = ∏_{i<j}(X_i − X_j)². This polynomial is symmetric. Indeed, a permutation π sends the factor for {i,j} to the squared difference belonging to {π(i),π(j)}. Sorting the latter pair into increasing order changes a difference at most by a sign, and its square is unchanged. The map on unordered two-element subsets is bijective, with inverse induced by π⁻¹. Thus this operation only reindexes the finite product and leaves P unchanged.
5. Apply MvPolynomial.esymmAlgHom_surjective over ℤ with variable set Fin n and n elementary symmetric generators; its cardinality hypothesis is Fintype.card (Fin n) = n. There is Q ∈ ℤ[Y_0,…,Y_{n−1}] such that P = Q(e_1,…,e_n), where e_k is the kth elementary symmetric polynomial in the X_i. This is precisely the substitution sending Y_i to e_{i+1} in the cited theorem from Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean.
6. Expanding the factorization in step 2, the coefficient of X^(n−k), for 1 ≤ k ≤ n, is (−1)^k e_k(β). To obtain that coefficient, one selects the constant term from exactly k of the n linear factors, giving the sum of their k-fold root products and the sign (−1)^k. On the other hand, this coefficient is the image of f.coeff (n−k). Multiplying by (−1)^k therefore gives e_k(β) = ((−1)^k f.coeff (n−k) : E). This also follows from Polynomial.coeff_eq_esymm_roots_of_splits in Mathlib/RingTheory/Polynomial/Vieta.lean. Define integers c_i = (−1)^(i.val+1) f.coeff (n−(i.val+1)) for i : Fin n.
7. Define D to be the integer obtained by evaluating Q at the family c. Applying the integer-to-E ring homomorphism commutes with polynomial evaluation. Using steps 5 and 6, its image is Q(e_1(β),…,e_n(β)) = P(β) = ∏_{i<j}(β i − β j)². This is exactly the filtered-finset product in the statement.
8. For every indexed pair i < j, injectivity of β gives β i ≠ β j. Each corresponding squared difference is therefore nonzero. A finite product of nonzero elements of a field is nonzero, including the empty product, which is 1. Hence the image of D is nonzero, so D ≠ 0. The witnesses n, β, and D satisfy every required assertion.

## Key steps

1. Identify the integer minimal polynomial with the rational minimal polynomial after coefficient extension.
2. Use normality and separability to enumerate the roots injectively and factor the polynomial.
3. Prove root integrality and coverage of every rational automorphic conjugate.
4. Show that the product of squared variable differences is symmetric by reindexing unordered pairs.
5. Express that product in elementary symmetric polynomials over ℤ.
6. Use Vieta's identities to evaluate those generators at integer coefficients and obtain D.
7. Use distinctness of the roots to prove the product, and therefore D, is nonzero.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/785

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
