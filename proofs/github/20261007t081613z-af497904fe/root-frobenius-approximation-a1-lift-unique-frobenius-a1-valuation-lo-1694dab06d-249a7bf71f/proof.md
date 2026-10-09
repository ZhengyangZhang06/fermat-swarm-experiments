# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, ℓ, and V satisfying the hypotheses. The inherited characteristic-zero field structure and finite rational dimension make E a number field. By the pinned Mathlib/NumberTheory/NumberField/Basic.lean, its integer ring O_E is a finite free ℤ-module, is Dedekind, and has fraction field E. Let m_V denote the maximal ideal of V, identified with V.nonunits after embedding in E.
2. Every algebraic integer a ∈ O_E belongs to V. Indeed, suppose a ∉ V. Then a ≠ 0, and the valuation-ring property puts a⁻¹ in V. It is a nonunit there, since an inverse in V would equal a. Choose a monic integral equation a^n + c_{n-1}a^{n-1} + ⋯ + c_0 = 0, where n ≥ 1 and the c_i are integers. All integers belong to V. Dividing by a^n gives 1 = −∑_{i<n} c_i(a⁻¹)^{n-i}. Each summand belongs to m_V, so 1 ∈ m_V, a contradiction.
3. The inclusion O_E → E therefore factors through V. Define q as the inverse image of m_V under O_E → V. Contraction of a proper prime ideal is a proper prime ideal, so q is prime. The assumption V.LiesOverPrime ℓ says precisely that the image of ℓ belongs to m_V; hence ℓ ∈ q. Since ℓ is prime, it is nonzero, and characteristic zero makes its image in O_E nonzero. Thus q ≠ 0. By its definition, q also satisfies a ∈ q if and only if the image of a belongs to V.nonunits, for every a ∈ O_E.
4. Form A = (O_E)_q and identify it with its image in E. This localization embeds in E because its denominators are nonzero and E is the fraction field of O_E. Its image consists exactly of fractions a/b with a,b ∈ O_E and b ∉ q. The pinned theorem IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain makes A a DVR, hence a valuation ring. Its maximal ideal consists of the fractions a/b with a ∈ q and b ∉ q.
5. If b ∉ q, its image belongs to V but not to m_V, and therefore is a unit of V. Consequently every fraction defining A belongs to V. Moreover, a fraction in the maximal ideal of A maps into m_V: its numerator maps into m_V and its denominator is a unit. Thus A ⊆ V and the inclusion carries the maximal ideal of A into m_V.
6. Conversely, suppose x ∈ E lies outside A. Then x ≠ 0. Since A is a valuation ring, x⁻¹ belongs to A; it is a nonunit of A, because an inverse in A would equal x. Step 5 puts x⁻¹ in m_V. Therefore x cannot belong to V, since otherwise x would invert an element of m_V. This proves V = A as subrings of E and proves the required fraction-membership equivalence.
7. Finally, choose a finite ℤ-basis of O_E, of size d. Modulo ℓO_E, each basis coefficient can be reduced modulo ℓ, so O_E/ℓO_E is a quotient of the finite set (ℤ/ℓℤ)^d and is finite. Since ℓ ∈ q, the quotient map to O_E/q factors through O_E/ℓO_E and is surjective. Hence O_E/q is finite. Together with steps 3 and 6, this proves every asserted property of q.

## Key steps

1. Show that every algebraic integer lies in the valuation ring by dividing a monic equation by its highest power.
2. Contract the maximal ideal to obtain a nonzero prime ideal containing ℓ.
3. Embed the DVR localization into V and show that its maximal ideal maps into the maximal ideal of V.
4. Use inverses of elements outside the localization to prove equality with V.
5. Use a finite integral basis modulo ℓ to prove finiteness of the residue quotient.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|LiesOverPrime|stabilizerHom_surjective|isDiscreteValuationRing_of_dedekind_domain`
- `RingOfIntegers|isDedekindDomain|isFractionRing|finite|free`
- `exists.*[Ff]robenius|[Ff]robenius.*exists|lift.*[Ff]robenius`
- `nonunits|mem_nonunits|isUnit`
- `exists.*[Ll]iesOver|exists.*[Uu]nder|exists_ideal_over|liesOver`
- `fixedField.*bot|fixed_by_all|mem_bot|mem_range|fixedField_top|isInvariant`
- `p09_af497904fe_luf_`
- `python3 .humanize/luf-split-diagnostic-20261009/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/GoingUp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Invariant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Invariant/Galois.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Frobenius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Galois/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/luf-split-diagnostic-20261009/Types.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/luf-split-diagnostic-20261009/Types.lean.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/luf-split-diagnostic-20261009/report.json`

The snapshots are clean at project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; compiler dependencies also match their clean pinned revisions. The inspected files supply integer-ring finiteness and Dedekind properties, DVR localizations, integral prime lifting, fixed-ring identification, residue-action surjectivity, and the exact valuation Frobenius predicates. The targeted lifting search found no direct implementation of the supplied algebraic-closure lifting statement in the searched directories. All four proposed types elaborate after import Submission. Additional checks verify integer-ring actions, field inclusions, automorphism multiplication, and the frozen residue action. Checked types and supporting declarations depend only on propext, Classical.choice, and Quot.sound. Proposed names were absent from the active DAG and imported environment. The successful diagnostic receipt records policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, omission of precisely lines 10–11, reversible original/build hashes, a successful Lean absence probe for all eight targets, and unchanged protected files. These are interface diagnostics, not proof or comparator acceptance.
