<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.invariant_conull_core-a1 -->

## Theorem `Submission.f036cc6b1f_pic_mec_invariant_conull_core`

Let G = SL₂(ℤ) act canonically on the upper half-plane ℍ, equipped with hyperbolic measure μ = dx dy/y². Let Δ ≤ G be any subgroup, and let S ⊆ ℍ be measurable with z ∈ S for μ-almost every z. Then there exists a measurable set X ⊆ S such that z ∈ X for μ-almost every z and, for every γ ∈ Δ and every z ∈ ℍ, γz ∈ X if and only if z ∈ X.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.invariant_conull_core-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/211

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pic_mec_invariant_conull_core`

```lean
∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (S : Set UpperHalfPlane), MeasurableSet S → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ S) → ∃ X : Set UpperHalfPlane, MeasurableSet X ∧ (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ X) ∧ X ⊆ S ∧ (∀ (γ : Δ) (z : UpperHalfPlane), (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X)
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

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.invariant_conull_core-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Δ and S satisfying the hypotheses, and write μ for hyperbolic volume. The map sending an element of SL₂(ℤ) to its four integer entries is injective. Since a finite product of countable sets is countable, SL₂(ℤ) is countable, and its subtype Δ is countable.
2. For every g ∈ SL₂(ℤ), let T_g(z) = gz. The canonical action is the GL₂(ℝ) action of Matrix.SpecialLinearGroup.mapGL ℝ g. The pinned UpperHalfPlane.instContinuousGLSMul makes T_g continuous, hence measurable for the Borel measurable structure on ℍ. The GL₂(ℝ)-invariance of hyperbolic volume in UpperHalfPlane/Measure.lean, together with MeasureTheory.measurePreserving_smul, shows that T_g preserves μ. Consequently μ(T_g⁻¹(C)) = μ(C) for every measurable C ⊆ ℍ.
3. Put N = ℍ \ S. This set is measurable because S is measurable. The assumption that z ∈ S almost everywhere says exactly that μ(N) = 0.
4. Define N* = ⋃δ∈Δ T_δ⁻¹(N). Each constituent is measurable by step 2 and has measure μ(N) = 0. Because Δ is countable, N* is measurable and null: countable subadditivity bounds its measure by a countable sum of zeros. Put X = ℍ \ N*. Then X is measurable and its complement has measure zero, so z ∈ X almost everywhere.
5. The identity belongs to Δ, and T_1 is the identity map. Therefore N ⊆ N*. Taking complements gives X ⊆ S.
6. Suppose z ∈ X and η ∈ Δ. For every δ ∈ Δ, the product δη belongs to Δ. Membership in X means that no Δ-translate of z belongs to N. Thus δ(ηz) = (δη)z does not belong to N for every δ ∈ Δ. By the definition of N*, this says ηz ∈ X.
7. Conversely, suppose ηz ∈ X. Apply step 6 to the point ηz and the subgroup element η⁻¹. It gives η⁻¹(ηz) ∈ X, hence z ∈ X. Combining this with step 6 proves ηz ∈ X if and only if z ∈ X. Together with steps 4 and 5, this establishes every required property of X.

## Key steps

1. Establish countability of SL₂(ℤ) and its subgroup Δ using integer matrix entries.
2. Identify each action map with a continuous, hyperbolic-measure-preserving GL₂(ℝ) action.
3. Take the measurable null complement of S.
4. Saturate that complement by countably many action preimages and take its complement X.
5. Use the identity to prove X ⊆ S.
6. Use closure under multiplication and inversion to prove exact Δ-invariance.

## Reference use

### local-project

Queries:
- `SL_neg_smul|measurePreserving.*(smul|SMul)|span_heckeTLin_eigen_eq_top|measurable.*(fundamental|Fundamental)|IsFundamentalDomain`
- `measurePreserving|continuous.*smul|mapGL|volume`
- `invariant.*conull|conull.*invariant|equidecomposition|unique.*sign`
- `neg_inv|inv_neg|hasDistribNeg|DistribNeg|Neg.*SL|instNeg|neg_neg`
- `f036cc6b1f_pic_mec_invariant_conull_core|f036cc6b1f_pic_mec_pointwise_sign_partition`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false /tmp/fermat-p01-mec-decomposition-check/Check.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/Action.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/FundamentalDomain.lean`
- `/tmp/fermat-p01-mec-decomposition-check/Check.lean`
- `/tmp/fermat-p01-mec-decomposition-check/Check-configured.log`
- `/tmp/fermat-p01-mec-decomposition-check/types.json`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Measure.lean defines hyperbolic volume and proves GL₂(ℝ)-invariance; Topology.lean supplies continuous action maps; MoebiusAction.lean identifies the SL action through mapGL and supplies ModularGroup.SL_neg_smul. SpecialLinearGroup.lean supplies matrix negation and HasDistribNeg. FundamentalDomain.lean requires disjointness of group translates, so its domain results cannot be applied directly to Δ when −I acts trivially. The targeted project/Definitions search found no relevant invariant-conull-core or sign-equidecomposition declaration. Both proposed identifiers were absent from the searched DAG and node artifacts. Both final types elaborate after literal import Submission, with exit code 0. Instance inspection confirmed UpperHalfPlane.instMeasureSpace and UpperHalfPlane.SLAction; an anonymous check established countability explicitly. The audited action, continuity, volume, and measure-invariance declarations use only propext, Classical.choice, and Quot.sound as transitive axioms. All nine dependency repositories were clean at their pinned revisions, and all twenty rebuilt local import sources matched the snapshot. These are interface and infrastructure checks, not comparator acceptance of the proposed child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/309

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
