# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1.ideal_inertia_to_valuation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, q, and P satisfying the hypotheses, and put O = NumberField.RingOfIntegers E. Since E is finite-dimensional over ℚ, it is a number field; the corresponding structure is supplied by NumberField.of_module_finite ℚ E. Consequently O is a Dedekind domain with fraction field E. The contraction hypothesis implies q ∈ P. Since q is prime and E has characteristic zero, its image in O is nonzero. Thus P is nonzero, and a nonzero prime ideal of the Dedekind domain O is maximal.
2. Let S = O \ P. Since P is prime, S is multiplicatively closed and does not contain zero. The localization S⁻¹O embeds in E by a/b ↦ a/b. This map is injective because O embeds in its fraction field E. Its image is the subring V = {a/b : a,b ∈ O and b ∉ P}. The theorem IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain makes S⁻¹O, and hence V, a discrete valuation ring. Moreover E is the fraction field of V: O is contained in V, and every element of E is a quotient of elements of O. A discrete valuation ring is a valuation ring of its fraction field, so V defines a valuation subring of E.
3. Since P is maximal, O/P is a field. Define φ : V → O/P by φ(a/b) = ā/b̄. Here b̄ is nonzero because b ∉ P. This is well-defined: equality a/b = c/d in E implies ad = cb in O, hence ā d̄ = c̄ b̄ in O/P. The usual common-denominator identities show that φ is a ring homomorphism. It is surjective because every class ā is φ(a/1). Its kernel consists precisely of the fractions with numerator in P. Therefore its kernel is a maximal ideal; since V is local, this is the unique maximal ideal of V. In particular, q/1 lies in that maximal ideal, so q is a nonunit in V and V.LiesOverPrime q holds. The induced isomorphism V/ker φ ≅ O/P identifies the residue field of V with O/P.
4. Let σ ∈ I = P.inertia G, where G = Autℚ(E). Rational automorphisms preserve O: applying σ to a monic integer polynomial equation preserves that equation, and the same argument applies to σ⁻¹. By the definition of I, σ(a) − a ∈ P for every a ∈ O. Hence σ sends P into P. Since I is a subgroup, σ⁻¹ also belongs to I and sends P into P; consequently σ(P) = P. In particular, σ and σ⁻¹ both preserve O \ P. Thus σ(a/b) = σ(a)/σ(b) belongs to V whenever a/b belongs to V, and the inverse automorphism has the same property. It follows that σ stabilizes V and determines an element of V.decompositionSubgroup ℚ.
5. For a/b ∈ V, the inertia congruences give overline(σ(a)) = ā and overline(σ(b)) = b̄. Therefore φ(σ(a/b)) = overline(σ(a))/overline(σ(b)) = ā/b̄ = φ(a/b). Under the residue-field identification from step 3, the induced action of σ on the residue field of V is the identity.
6. By definition, V.inertiaSubgroup ℚ is the kernel of the residue action of V.decompositionSubgroup ℚ. Steps 4 and 5 put the decomposition-group element represented by σ in this kernel. The definition of V.inertiaSubgroupIn ℚ maps that kernel into G, so σ ∈ V.inertiaSubgroupIn ℚ. Since σ was arbitrary in I, I ≤ V.inertiaSubgroupIn ℚ. Together with V.LiesOverPrime q from step 3, this proves the required existential statement.

## Key steps

1. Use finite-dimensionality to obtain a number field and show P is a nonzero maximal ideal.
2. Embed the localization O_P in E and use the Dedekind-domain localization theorem to obtain a valuation subring V.
3. Construct the surjective residue map a/b ↦ ā/b̄, identify its kernel, and deduce that q is a nonunit in V.
4. Show that ideal inertia preserves P, its complement, and therefore V.
5. Compute the induced residue action and show it is the identity.
6. Use the kernel-and-image definitions to obtain the required inertia subgroup inclusion.

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
