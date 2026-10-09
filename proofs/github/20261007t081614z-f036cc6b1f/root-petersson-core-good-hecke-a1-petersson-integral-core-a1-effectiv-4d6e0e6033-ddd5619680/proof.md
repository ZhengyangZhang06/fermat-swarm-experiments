# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1.sign_transversal-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Δ and the hypothesis −I ∈ Δ. For g ∈ Δ, matrix multiplication gives (−I)g = −g, so subgroup closure implies −g ∈ Δ. Entrywise negation satisfies −(−g) = g. Thus negation induces an involution on Δ.
2. Define a relation on Δ by p ∼ q if p̄ = q̄ or p̄ = −q̄. It is reflexive by equality. For symmetry, equality is symmetric, and p̄ = −q̄ implies q̄ = −p̄ by negating both sides and using double negation. For transitivity, suppose p ∼ q and q ∼ r. If p̄ = q̄ and q̄ = r̄, then p̄ = r̄. If p̄ = q̄ and q̄ = −r̄, then p̄ = −r̄. If p̄ = −q̄ and q̄ = r̄, then p̄ = −r̄. If p̄ = −q̄ and q̄ = −r̄, then p̄ = −(−r̄) = r̄. These exhaust the possibilities, so ∼ is an equivalence relation.
3. Let Q be the quotient of Δ by this equivalence relation. Every quotient class has a representative in Δ. By classical choice choose a function s : Q → Δ satisfying [s(c)] = c for every c ∈ Q; this is the quotient representative construction supplied by Quotient.out and Quotient.out_eq. Define L to be the range of s.
4. Given δ : Δ, put γ = s([δ]). Then γ ∈ L and [γ] = [δ]. Equality of classes for this equivalence relation gives γ ∼ δ. By definition, γ̄ = δ̄ or γ̄ = −δ̄, proving the covering property.
5. Suppose γ,η ∈ L and γ̄ = η̄ or γ̄ = −η̄. Choose c,d ∈ Q with γ = s(c) and η = s(d). The sign condition gives γ ∼ η and hence [γ] = [η]. Since [s(c)] = c and [s(d)] = d, it follows that c = d. Applying s gives γ = η as elements of Δ. Thus L has both required properties.

## Key steps

1. Use −I ∈ Δ to restrict involutive matrix negation to Δ.
2. Verify that equality up to sign is an equivalence relation.
3. Choose one representative of each quotient class and take the range.
4. Use the representative of [δ] to establish coverage.
5. Use equality of quotient classes to establish uniqueness inside the range.

## Reference use

### local-project

Queries:
- `SL_neg_smul|instContinuousGLSMul|transversal|fundamental.*(partition|domain)|exists.*representative`
- `neg_mul|mul_neg|neg_inv|inv_neg|neg_neg|neg_one`
- `exists.*[Rr]ep|exists.*[Oo]ut|range.*[Oo]ut|out_eq|out_equiv|out.*mk|exists.*[Tt]ransversal`
- `sign.*(partition|transversal)|measurable.*equidecomp|pointwise_sign_partition`
- `IsFundamentalDomain|pairwise|Pairwise|disjoint|iUnion`
- `borel|BorelSpace|MeasurableSpace`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Data/Quot.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/FundamentalDomain.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-effectiv-f2ec3caac6/decomposition-checks-psp/FrozenTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-effectiv-f2ec3caac6/decomposition-checks-psp/FrozenTypes.log`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The snapshot supplies ModularGroup.SL_neg_smul, UpperHalfPlane.instContinuousGLSMul, the canonical Borel structure, HasDistribNeg for the special linear group, and Quotient.out representative lemmas. IsFundamentalDomain uses almost-everywhere disjointness and does not directly provide the required exact partition. The targeted project search found no matching sign-partition or measurable-equidecomposition theorem. Both proposed types elaborated after import Submission; an rfl check verified that the inferred action agrees with mapGL ℝ, and instance synthesis returned UpperHalfPlane.SLAction.toSMul and UpperHalfPlane.instBorelSpace. All nine dependency checkouts were clean and matched their pinned revisions; reused compiled project imports had source files identical to the frozen snapshot. The checked library declarations depend only on propext, Classical.choice, and Quot.sound. These are interface and library checks, not comparator acceptance of child proofs.
