# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_cyclotomic_character-a1`
- Child DAG node: `root.finite_cyclotomic_character-a1.frobenius_roots_action-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N, ℓ, P and σ satisfying the hypotheses, and write μ = {η ∈ Ω : η^N = 1}. Every η ∈ μ is nonzero because N > 0. We have η⁻¹ = η^(N−1), and also η = (η⁻¹)^(N−1). The valuation-subring property gives η ∈ P or η⁻¹ ∈ P. In the second case, closure under powers and the latter identity give η ∈ P as well. The former identity then gives η⁻¹ ∈ P. Thus every element of μ belongs to P and is a unit of P.
2. Let k be the residue field of the local ring P, and let red : P → k be the residue homomorphism. The hypothesis P.LiesOverPrime ℓ says that ℓ is a nonunit of P. Nonunits of a local ring form its maximal ideal, so red(ℓ) = 0. The kernel of the unital map ℤ → k is a proper ideal containing ℓℤ. Since ℓ is prime, ℓℤ is maximal; therefore this kernel equals ℓℤ. Consequently k has characteristic ℓ. In particular, the image of N in k is nonzero because ℓ does not divide N.
3. Suppose ξ ∈ μ has residue one. If ξ ≠ 1, the geometric-sum identity gives (ξ − 1)(1 + ξ + ⋯ + ξ^(N−1)) = ξ^N − 1 = 0 in Ω. Since Ω is a field and ξ − 1 ≠ 0, the sum is zero. Every term belongs to P by step 1, and the inclusion P → Ω is injective, so the same sum is zero in P. Reducing it gives 1 + 1 + ⋯ + 1 = 0 with N terms, contradicting the nonvanishing of N in k established in step 2. Therefore ξ = 1.
4. Reduction is injective on μ. Indeed, suppose η and θ belong to μ and have equal residues. Step 1 shows that θ and θ⁻¹ are units in P, so their residues are mutually inverse and nonzero. The element ξ = ηθ⁻¹ belongs to P, satisfies ξ^N = η^N(θ^N)⁻¹ = 1, and has residue red(η)red(θ)⁻¹ = 1. Step 3 gives ξ = 1, hence η = θ.
5. Unpack P.IsFrobeniusAt σ ℓ. It supplies membership of σ in the decomposition subgroup of P and asserts that its induced action on k is x ↦ x^ℓ. Membership in the decomposition subgroup makes σ an automorphism of P. By the definition of the induced residue action, red(σ(u)) equals the action of σ on red(u) for every u ∈ P. Hence red(σ(u)) = red(u)^ℓ = red(u^ℓ).
6. Now let ζ ∈ Ω satisfy ζ^N = 1. Step 1 allows us to apply step 5 to ζ, yielding equal residues for σ(ζ) and ζ^ℓ. Both elements lie in μ: (σ(ζ))^N = σ(ζ^N) = 1, and (ζ^ℓ)^N = (ζ^N)^ℓ = 1. Injectivity from step 4 therefore gives σ(ζ) = ζ^ℓ, as required.
7. No step excludes N = 1. In that case ζ^N = 1 forces ζ = 1, and the conclusion is σ(1) = 1^ℓ = 1.

## Key steps

1. Use the valuation dichotomy and root-of-unity identities to place every root and its inverse in P.
2. Identify the kernel of ℤ → k(P) as ℓℤ and conclude that N is nonzero in the residue field.
3. Use the geometric-sum identity to show that a root reducing to one equals one.
4. Apply this result to quotients to prove injectivity of reduction on the N-th roots of unity.
5. Unpack Frobenius and residue-action compatibility to obtain equal reductions of σ(ζ) and ζ^ℓ.
6. Check both elements remain N-th roots of unity and apply injectivity.
7. Include the case N = 1.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|LiesOverPrime|cyclotomic|Cyclotomic|rootsOfUnity|IsPrimitiveRoot`
- `exists_primitiveRoot|natCard_rootsOfUnity|autToPow|pow_inj|pow_eq_one|mem_or_inv_mem|residue.*smul|smul.*residue`
- `frobenius.*rootsOfUnity|rootsOfUnity.*frobenius|IsFrobeniusAt.*pow|FrobeniusAt.*cyclotomic|cyclotomic.*FrobeniusAt`
- `IsAlgClosed|hasEnoughRootsOfUnity|HasEnoughRootsOfUnity`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RootsOfUnity/EnoughRootsOfUnity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RootsOfUnity/AlgebraicallyClosed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596`

The manifest pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. LiesOverPrime means the prime is a nonunit; IsFrobeniusAt specifies membership in the decomposition subgroup and the power action on the residue field. Mathlib supplies primitive-root existence, IsPrimitiveRoot.autToPow, autToPow_spec, eq_pow_of_pow_eq_one, and modularCyclotomicCharacter.spec/unique. The valuation files supply the valuation dichotomy and decomposition-group action. The targeted search for a Frobenius roots-of-unity action theorem returned no matches. Installed dependencies were checked clean at their pinned revisions. Lean checked the proposed types and the cited primitive-root declarations; their axiom lists contain only propext, Classical.choice, and Quot.sound.
