# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1.measurable_slice_partition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Δ,L,P,S,X and all the stated hypotheses. For g ∈ G write T_g(z) = gz. The canonical action is definitionally the action through Matrix.SpecialLinearGroup.mapGL ℝ. Therefore UpperHalfPlane.instContinuousGLSMul makes T_g continuous. Since ℍ carries its Borel measurable structure, T_g is measurable. Also ModularGroup.SL_neg_smul gives T_{−g}(z) = T_g(z) for every g and z.
2. Define Cγ exactly as in the statement. Fix γ : Δ. If γ ∉ L, the defining membership condition is impossible, so Cγ = ∅ and is measurable. If γ ∈ L, then Cγ = (P ∩ X) ∩ T_γ̄⁻¹(S), where the last expression denotes set preimage. The sets P and X are measurable, and the preimage of the measurable set S under the measurable map T_γ̄ is measurable. Their intersection is measurable. Hence every Cγ is measurable.
3. To prove pairwise disjointness, suppose z ∈ Cγ ∩ Cη. Then γ,η ∈ L, z ∈ X, and γ̄z,η̄z ∈ S. Choose the witness r from the hypothesis for S at z. The subgroup memberships of γ̄ and η̄ and their images in S imply γ̄ = r or γ̄ = −r, and η̄ = r or η̄ = −r. If both equal r, or both equal −r, then γ̄ = η̄. If γ̄ = r and η̄ = −r, then γ̄ = −η̄ by double negation. If γ̄ = −r and η̄ = r, then again γ̄ = −η̄. Thus γ̄ = η̄ or γ̄ = −η̄. The uniqueness hypothesis on L yields γ = η. Consequently distinct indices have no common point in their pieces, proving pairwise disjointness.
4. Every Cγ is contained in P ∩ X directly from its definition. Thus ⋃γ Cγ ⊆ P ∩ X. Conversely, let z ∈ P ∩ X. Apply the hypothesis for S to z ∈ X to obtain r ∈ Δ with rz ∈ S. Regard r together with its subgroup-membership proof as an element δ : Δ. The covering hypothesis on L gives γ ∈ L with γ̄ = r or γ̄ = −r. In the first case γ̄z = rz; in the second case the sign invariance from step 1 gives the same equality. Hence γ̄z ∈ S. Together with γ ∈ L and z ∈ P ∩ X, this proves z ∈ Cγ and therefore z ∈ ⋃γ Cγ. The two inclusions establish ⋃γ Cγ = P ∩ X.
5. Combining the measurability from step 2, pairwise disjointness from step 3, and union identity from step 4 gives exactly the asserted conjunction for the specified family C.

## Key steps

1. Obtain measurability and sign invariance of each canonical action map.
2. Express each nonempty slice as an intersection with a measurable preimage.
3. Reduce intersecting slices to indices equal up to sign, then use uniqueness in L.
4. Use an orbit witness and the covering property of L to cover every point of P ∩ X.
5. Combine measurability, pairwise disjointness, and exact coverage.

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
