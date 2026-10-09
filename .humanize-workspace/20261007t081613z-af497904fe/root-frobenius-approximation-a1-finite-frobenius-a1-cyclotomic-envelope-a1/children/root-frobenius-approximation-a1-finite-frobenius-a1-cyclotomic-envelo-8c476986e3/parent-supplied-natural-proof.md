# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.compositum_pair-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, C, g, and a, and put M = EC inside Ω. The products of elements from finite rational bases of E and C span a finite-dimensional subalgebra containing both fields. A finite-dimensional domain over a field is a field, so this subalgebra is M and M is finite-dimensional. Both E and C are splitting fields of separable polynomials over ℚ; the union of these sets of roots generates M. Thus M/ℚ is normal and separable, hence Galois. Also M/C is finite Galois.
2. Restriction defines a homomorphism r : Gal(M/C) → Gal(E/ℚ). It is well-defined because E/ℚ is normal. It is injective: an element in its kernel fixes E and C, and therefore fixes the field they generate, namely M.
3. Write J for the image of r. An element x of E is fixed by J exactly when it is fixed by every element of Gal(M/C). By finite Galois correspondence for M/C, this is equivalent to x belonging to C. Thus the fixed field E^J is E ∩ C = ℚ. Finite Galois correspondence for E/ℚ now gives J = Gal(E/ℚ). Hence r is bijective, and [M:C] = |Gal(M/C)| = |Gal(E/ℚ)| = [E:ℚ].
4. Simultaneous restriction gives R : Gal(M/ℚ) → Gal(E/ℚ) × Gal(C/ℚ). Both restrictions are well-defined by normality. If two automorphisms have the same restrictions, their equalizer is an intermediate field containing E and C, so it is M; therefore R is injective. The degree formula and step 3 give |Gal(M/ℚ)| = [M:ℚ] = [M:C][C:ℚ] = [E:ℚ][C:ℚ], equal to the cardinality of the product target. Consequently R is bijective.
5. Let h be the unique inverse image under R of (g,a). The two coordinates of R(h) = (g,a), expressed through the canonical inclusions of E and C into M, are exactly the two families of equations in the statement. Injectivity of R proves uniqueness.

## Key steps

1. Show the compositum is finite Galois over ℚ and Galois over C.
2. Restrict Gal(M/C) injectively to Gal(E/ℚ).
3. Identify the fixed field of the restriction image with E ∩ C and conclude surjectivity.
4. Use the resulting degree equality to make simultaneous restriction bijective.
5. Take the unique inverse image of the prescribed pair.

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
