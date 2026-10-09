# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.fraction_characterization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, V, and q with all the stated hypotheses, and write O = NumberField.RingOfIntegers E. The inherited characteristic-zero structure and finite rational dimension make E a number field. By the pinned Mathlib/NumberTheory/NumberField/Basic.lean, O is a Dedekind domain and E is its fraction field. Write m_V for the maximal ideal of V; its image in E is V.nonunits by ValuationSubring.coe_mem_nonunits_iff.
2. Let S = O \ q. Since q is prime and proper, S is multiplicatively closed, contains 1, and does not contain 0. Form A = S⁻¹O and embed it into E by a/b ↦ (a : E)/(b : E). This is an injective ring homomorphism: the denominators are nonzero in E, and a fraction mapping to zero has zero numerator because O embeds injectively into E. Identify A with its image. Its elements are exactly the fractions with numerator in O and denominator outside q. It contains O through a ↦ a/1. Since every element of E is a quotient of elements of O, E is also the fraction field of A. These constructions are provided by Mathlib/RingTheory/Localization/AsSubring.lean.
3. As q is nonzero and prime, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain, in Mathlib/RingTheory/DedekindDomain/Dvr.lean, makes A a discrete valuation ring. In particular A is a valuation ring. Its maximal ideal m_A consists exactly of fractions a/b with a ∈ q and b ∉ q. Indeed, IsLocalization.AtPrime.to_map_mem_maximal_iff identifies the preimage of m_A in O with q; the image of every denominator b ∉ q is a unit, so multiplying by its inverse preserves membership in m_A. Equivalently, this is IsLocalization.AtPrime.mk'_mem_maximal_iff in Mathlib/RingTheory/Localization/AtPrime/Basic.lean.
4. Let b ∈ O satisfy b ∉ q. Its image belongs to V by the containment hypothesis. The center-compatibility hypothesis says this image is not in V.nonunits, so the corresponding element of V is a unit. Its inverse in V maps to (b : E)⁻¹. Therefore every fraction a/b defining A belongs to V, proving A ⊆ V. If a/b belongs to m_A, step 3 gives a ∈ q. Center compatibility then places the numerator in m_V, and multiplication by the denominator's inverse in V keeps the fraction in m_V. Thus the inclusion A → V carries m_A into m_V.
5. Suppose x ∈ E lies outside A. Since 0 ∈ A, x ≠ 0. Because A is a valuation ring with fraction field E, x⁻¹ belongs to A. To see the fraction-field alternative explicitly, write x = r/s with r,s ∈ A and s ≠ 0. Divisibility in a valuation ring is total: if s divides r then x ∈ A, while if r divides s then, since x ≠ 0, x⁻¹ ∈ A. The first case is excluded. Moreover x⁻¹ is a nonunit of A, since an inverse in A would equal x in E. Hence x⁻¹ ∈ m_A, and step 4 puts its image in m_V. If x also belonged to V, the ideal m_V would contain x·x⁻¹ = 1, contradicting its properness. Therefore x ∉ V.
6. Step 4 proves A ⊆ V and step 5 proves V ⊆ A. Consequently x ∈ V if and only if x ∈ A. Substituting the description of A from step 2 yields exactly: x ∈ V if and only if there exist a,b ∈ O with b ∉ q and x = (a : E)/(b : E).

## Key steps

1. Use the number-field structure to obtain the Dedekind integer ring and its fraction field E.
2. Embed the localization at O_E \ q into E and identify its elements with the stated fractions.
3. Use nonzeroness of q to make the localization a DVR and identify its maximal ideal by numerator membership.
4. Use integral containment and center compatibility to embed the localization into V while preserving maximal-ideal membership.
5. For an element outside the localization, place its inverse in the localization's maximal ideal and exclude the element from V.
6. Combine both inclusions and unfold localization membership.

## Reference use

### local-project

Queries:
- `LiesOverPrime|isDiscreteValuationRing_of_dedekind_domain|finite_quotient|nonunits`
- `integral|IntegrallyClosed|eq_of|localization|Localization|nonunits`
- `valuationSubring|ValuationSubring`
- `isIntegral|IsIntegral|isIntegrallyClosed|integralClosure`
- `p09_af497904fe_vloc_integral_center|p09_af497904fe_vloc_fraction_characterization`
- `python3 .humanize/vloc-split-diagnostic-k9wikt8l/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Localization/AsSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Localization/AtPrime/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/LocalSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/IntegralClosure`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/Integral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/vloc-split-diagnostic-k9wikt8l/Types.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/vloc-split-diagnostic-k9wikt8l/Types.lean.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/vloc-split-diagnostic-k9wikt8l/report.json`

The snapshots match project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d with clean tracked files; compiler dependencies match their clean pinned revisions. The inspected sources supply integer-ring integrality, finite freeness, Dedekind and fraction-field structures, embedded localizations, the DVR theorem, and localization maximal-ideal membership. LiesOverPrime is exactly membership of the prime's image in V.nonunits. The search for valuationSubring|ValuationSubring returned no matches in IntegralClosure or Valuation/Integral.lean; the broader search located integrally-closed instances in Valuation/LocalSubring.lean. Both proposed types elaborate after import Submission in the policy-authorized disposable copy. Additional examples check canonical integer-ring coercions, field division, nonunits interpretation, and the required number-field instances. The checked types and supporting declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. Both proposed names are absent from the active DAG and imported environment. The diagnostic receipt records the required policy digest, omission of precisely lines 10–11, reversible original/build hashes, successful absence checks for all eight targets, and unchanged protected files. These are interface diagnostics, not comparator acceptance.
