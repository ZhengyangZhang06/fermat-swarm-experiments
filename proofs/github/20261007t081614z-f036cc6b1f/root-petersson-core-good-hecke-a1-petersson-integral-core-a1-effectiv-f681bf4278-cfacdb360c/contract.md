<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1.measurable_slice_partition-a1 -->

## Theorem `Submission.f036cc6b1f_pic_psp_measurable_slice_partition`

Let G = SL₂(ℤ) act canonically on the upper half-plane ℍ with its Borel measurable structure. Let Δ ≤ G be any subgroup, and write γ̄ for the underlying matrix of γ : Δ. Let L ⊆ Δ satisfy: every δ : Δ has some γ ∈ L with γ̄ = δ̄ or γ̄ = −δ̄; and any γ,η ∈ L whose underlying matrices are equal up to sign satisfy γ = η. Let P,S,X ⊆ ℍ be measurable. Assume that for every z ∈ X there exists r ∈ G with r ∈ Δ and rz ∈ S such that every δ ∈ G satisfying δ ∈ Δ and δz ∈ S obeys δ = r or δ = −r. Define Cγ = {z ∈ ℍ | γ ∈ L, z ∈ P ∩ X, and γ̄z ∈ S}. Then every Cγ is measurable, the family C : Δ → Set ℍ is pairwise disjoint, and ⋃γ Cγ = P ∩ X.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1.measurable_slice_partition-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/218

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pic_psp_measurable_slice_partition`

```lean
∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (L : Set Δ) (P S X : Set UpperHalfPlane), MeasurableSet P → MeasurableSet S → MeasurableSet X → (∀ δ : Δ, ∃ γ : Δ, γ ∈ L ∧ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(δ : Matrix.SpecialLinearGroup (Fin 2) ℤ))) → (∀ γ : Δ, γ ∈ L → ∀ η : Δ, η ∈ L → ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)) → γ = η) → (∀ z ∈ X, ∃ r : Matrix.SpecialLinearGroup (Fin 2) ℤ, r ∈ Δ ∧ r • z ∈ S ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ S → δ = r ∨ δ = -r) → let C : Δ → Set UpperHalfPlane := fun γ => {z | γ ∈ L ∧ z ∈ P ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ S}; (∀ γ, MeasurableSet (C γ)) ∧ Pairwise (fun γ η => Disjoint (C γ) (C η)) ∧ (⋃ γ, C γ) = P ∩ X
```

### Frozen project context

`Fermat/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean` at `61b5f85556ac71631ccad822e0694511234f7132` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

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


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/334

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
