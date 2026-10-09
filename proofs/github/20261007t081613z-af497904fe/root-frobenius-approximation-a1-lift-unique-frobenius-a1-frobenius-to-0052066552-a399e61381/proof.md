# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1.frobenius_from_exhaustive_restrictions-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write Ω = AlgebraicClosure ℚ and let ι_i : F_i → Ω be the inclusion. For each i choose g_i from the hypothesis. By the definition of IsFrobeniusAt, g_i belongs to the decomposition subgroup of V_i, so g_i maps V_i onto V_i. Consequently both g_i and g_i⁻¹ send elements of V_i into V_i.
2. For x ∈ F_i, agreement applied to g_i⁻¹(x) gives τ(ι_i(g_i⁻¹(x))) = ι_i(x). Applying τ⁻¹ proves τ⁻¹(ι_i(x)) = ι_i(g_i⁻¹(x)). Thus the given agreement also holds for the inverse automorphisms.
3. If z ∈ P, exhaustion gives i and x ∈ F_i with ι_i(x) = z. Exact restriction gives x ∈ V_i. Step 1 and agreement imply τ(z) ∈ P. Steps 1 and 2 imply τ⁻¹(z) ∈ P as well. The first inclusion gives τ(P) ⊆ P; for z ∈ P the second inclusion gives z = τ(τ⁻¹(z)) ∈ τ(P). Hence τ(P) = P, which means τ belongs to P.decompositionSubgroup ℚ. Denote this membership proof by hτ.
4. Exact restriction also identifies nonunits. Indeed, for x ∈ F_i, the criterion ValuationSubring.mem_nonunits_iff_or says that ι_i(x) ∈ P.nonunits if and only if ι_i(x) = 0 or ι_i(x)⁻¹ ∉ P. Injectivity and inverse preservation of ι_i, followed by exact restriction for x⁻¹, turn this into x = 0 or x⁻¹ ∉ V_i. Applying the criterion in V_i shows that this is equivalent to x ∈ V_i.nonunits.
5. Fix i and x ∈ V_i, with x viewed as an element of F_i when evaluating g_i. Let q_i be the residue homomorphism V_i → IsLocalRing.ResidueField V_i. The decomposition-group action on V_i is the restriction of g_i, and IsLocalRing.ResidueField.residue_smul identifies its residue action with q_i applied after this restriction. Thus the Frobenius hypothesis gives q_i(g_i(x)) = q_i(x)^ℓ = q_i(x^ℓ). Both g_i(x) and x^ℓ belong to V_i. Their difference d = g_i(x) − x^ℓ lies in V_i and satisfies q_i(d) = 0. The kernel of q_i is the maximal ideal, and ValuationSubring.coe_mem_nonunits_iff identifies its ambient image with V_i.nonunits. Hence d ∈ V_i.nonunits as an element of F_i.
6. For z ∈ P choose i and x ∈ V_i with ι_i(x) = z, using exhaustion and exact restriction as in step 3. Apply step 5 and then step 4 to obtain ι_i(g_i(x) − x^ℓ) ∈ P.nonunits. Since ι_i preserves subtraction and powers and τ(ι_i(x)) = ι_i(g_i(x)), this element equals τ(z) − z^ℓ. Consequently τ(z) − z^ℓ ∈ P.nonunits for every z ∈ P.
7. Let q_P : P → IsLocalRing.ResidueField P be the residue map. It is surjective, so any residue class a can be written q_P(z) for z ∈ P. By step 3, τ(z) defines an element of P. Step 6 and ValuationSubring.coe_mem_nonunits_iff put τ(z) − z^ℓ in the maximal ideal of P. Applying q_P gives q_P(τ(z)) = q_P(z)^ℓ. Compatibility of the residue map with the decomposition-group action identifies the left side with (τ,hτ) acting on a. Therefore (τ,hτ) acts by a ↦ a^ℓ on every residue class. Together with hτ this is exactly P.IsFrobeniusAt τ ℓ.

## Key steps

1. Choose the stage Frobenius automorphisms and establish inverse agreement.
2. Use exhaustion and exact restriction to show τ stabilizes P.
3. Identify nonunits under each field inclusion.
4. Translate each stage residue equation into a nonunit difference.
5. Transfer that difference to P and descend using residue-map surjectivity.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|LiesOverPrime|mem_nonunits_iff_or|decompositionSubgroup|residueFieldAut`
- `nonunits_comap|comap_nonunits|mem_nonunits.*comap|exists.*ValuationSubring|iUnion|directed|residue_surjective|residue.*smul|smul.*residue|residue_eq_zero_iff`
- `IsFrobeniusAt.*(iUnion|iSup|union)|(?:iUnion|iSup|union).*IsFrobeniusAt|nonunits_comap|comap_nonunits`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/fvu-decomposition-rnthom8q/final-report.json`

The snapshot pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. LiesOverPrime is nonunit membership; IsFrobeniusAt is decomposition-subgroup membership together with the residue power equation. The inspected nonunit criterion, maximal-ideal identification, residue surjectivity, and residue_smul support the proofs below. The final targeted search found no matching Frobenius-union or nonunit-comap lemma. Both exact child types elaborated after import Submission at frozen proof-base commit 97f32c2abc9205b480ae0c2cb521b382a16c3df0; inclusion and residue-action instance checks passed. Type and cited-library axiom checks found only propext, Classical.choice, and Quot.sound. The diagnostic report records clean pinned dependencies, authorized header omissions, their reversibility, and all eight target-absence checks. It separately records concurrent advancement of the working branch. These are interface diagnostics, not comparator acceptance.
