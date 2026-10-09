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
