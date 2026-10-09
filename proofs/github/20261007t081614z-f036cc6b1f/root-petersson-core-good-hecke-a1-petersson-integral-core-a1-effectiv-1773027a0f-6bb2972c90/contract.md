<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.integral_of_equidecomposition-a1 -->

## Theorem `Submission.f036cc6b1f_pic_dt_integral_of_equidecomposition`

Let α be a measurable space with measure μ, and let ι be a countable type. Let E,F ⊆ α and A_i,B_i ⊆ α be measurable sets. Assume that the A_i are pairwise disjoint, the B_i are pairwise disjoint, E agrees μ-almost everywhere with ⋃i A_i, and F agrees μ-almost everywhere with ⋃i B_i. Let T_i : α → α be measurable embeddings preserving μ, with T_i(A_i) = B_i for every i. If φ : α → ℂ is strongly measurable, satisfies φ(T_i x) = φ(x) for every i and x ∈ A_i, and is integrable on E, then φ is integrable on F and its integrals over E and F are equal.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.integral_of_equidecomposition-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/200

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pic_dt_integral_of_equidecomposition`

```lean
∀ (α ι : Type) [MeasurableSpace α] [Countable ι] (μ : MeasureTheory.Measure α) (E F : Set α) (A B : ι → Set α) (T : ι → α → α), MeasurableSet E → MeasurableSet F → (∀ i, MeasurableSet (A i)) → (∀ i, MeasurableSet (B i)) → Pairwise (fun i j => Disjoint (A i) (A j)) → Pairwise (fun i j => Disjoint (B i) (B j)) → (∀ᵐ x ∂μ, x ∈ E ↔ x ∈ ⋃ i, A i) → (∀ᵐ x ∂μ, x ∈ F ↔ x ∈ ⋃ i, B i) → (∀ i, MeasurableEmbedding (T i)) → (∀ i, MeasureTheory.MeasurePreserving (T i) μ μ) → (∀ i, T i '' A i = B i) → ∀ φ : α → ℂ, MeasureTheory.StronglyMeasurable φ → (∀ i, ∀ x ∈ A i, φ (T i x) = φ x) → MeasureTheory.IntegrableOn φ E μ → MeasureTheory.IntegrableOn φ F μ ∧ MeasureTheory.integral (μ.restrict E) φ = MeasureTheory.integral (μ.restrict F) φ
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

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.integral_of_equidecomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data and hypotheses. Put U = ⋃i A_i and V = ⋃i B_i. These sets are measurable because ι is countable. Almost-everywhere equality of sets gives equality of their restricted measures: μ restricted to E equals μ restricted to U, and μ restricted to F equals μ restricted to V. Thus φ is integrable on U, and it suffices to prove integrability on V and equality of the integrals over U and V.
2. For each i, the map T_i transports μ restricted to A_i to μ restricted to B_i. Indeed, let C ⊆ α be measurable. Injectivity of T_i and T_i(A_i) = B_i give A_i ∩ T_i⁻¹(C) = T_i⁻¹(B_i ∩ C). Because B_i ∩ C is measurable and T_i preserves μ, the two sides have measure μ(B_i ∩ C). This is exactly the equality of the restricted pushforward measure with μ restricted to B_i. Measurability of T_i supplies the measurable-map condition.
3. Define h(x) = ENNReal.ofReal(‖φ(x)‖). Strong measurability of φ implies measurability of this nonnegative extended-real function. Change of variables using step 2 gives ∫⁺_{B_i} h dμ = ∫⁺_{A_i} h(T_i x) dμ. On A_i the assumed equality φ(T_i x) = φ(x) implies h(T_i x) = h(x). Hence ∫⁺_{B_i} h dμ = ∫⁺_{A_i} h dμ for every i.
4. Countable additivity of nonnegative integrals over the two measurable disjoint families now gives ∫⁺_V h dμ = ∑i ∫⁺_{B_i} h dμ = ∑i ∫⁺_{A_i} h dμ = ∫⁺_U h dμ. The final quantity is finite because φ is integrable on U. Since φ is strongly measurable, it is almost everywhere strongly measurable for the restriction to V. The finite norm integral therefore proves that φ is integrable on V, and step 1 transfers this to F.
5. Every A_i lies in U and every B_i lies in V, so restriction of integrability shows that φ is integrable on each A_i and each B_i. The measurable-embedding change-of-variables formula, equivalently the restricted measure transport from step 2, gives ∫_{B_i} φ dμ = ∫_{A_i} φ(T_i x) dμ. The pointwise identity on A_i then gives ∫_{B_i} φ dμ = ∫_{A_i} φ dμ.
6. Countable additivity for Bochner integrals applies to the measurable disjoint partitions of U and V because φ is integrable on both unions. In particular, ∫_U φ dμ = ∑i ∫_{A_i} φ dμ and ∫_V φ dμ = ∑i ∫_{B_i} φ dμ. These series are absolutely convergent: the norm of each piece integral is at most the integral of ‖φ‖ over that piece, and the sums of those nonnegative bounds equal the finite norm integrals over U and V. Step 5 identifies the corresponding summands, so the integrals over U and V are equal. Finally step 1 identifies them with the integrals over E and F. Together with step 4, this proves the required conjunction.

## Key steps

1. Replace E and F by the almost-everywhere equal unions of their pieces.
2. Show each measurable embedding transports the restricted source measure to the restricted target measure.
3. Apply change of variables to the nonnegative norm and sum over the disjoint partitions.
4. Deduce integrability on the target union from strong measurability and finiteness of its norm integral.
5. Apply complex-valued change of variables on each piece.
6. Use countable additivity of Bochner integrals and restore E and F by equality of restricted measures.

## Reference use

### local-project

Queries:
- `fundamental|Fundamental|integral|volume|MeasurePreserving|SMulInvariant|invariant`
- `neg_smul|smul_neg|mapGL.*smul|smul.*mapGL|continuous.*[Ss][Ll]|specialLinear.*[Aa]ction|modular.*[Aa]ction`
- `integrableOn_iUnion|integral_iUnion|lintegral_iUnion|integrableOn_congr_set|setIntegral_congr_set|measurePreserving_smul|restrict_preimage|setIntegral_map|integral_comp`
- `domain_transfer|equidecomposition|unique.*sign|integrable.*fundamental|fundamental.*integral`
- `f036cc6b1f_pic_dt_measurable_equidecomposition|f036cc6b1f_pic_dt_integral_of_equidecomposition`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain --untracked-files=no`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/fermat-p01-domain-transfer-types-mz0mfqkj/Check.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/FundamentalDomain.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/tmp/fermat-p01-domain-transfer-types-mz0mfqkj/Check.lean`
- `/tmp/fermat-p01-domain-transfer-types-mz0mfqkj/Check.log`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Measure.lean supplies hyperbolic volume and GL₂(ℝ)-invariance; Topology.lean supplies continuous action maps; ModularGroup.sl_moeb and ModularGroup.SL_neg_smul identify the SL₂(ℤ) action and its sign invariance. FundamentalDomain.lean contains analogous integral-transfer results, but its pairwise-disjointness requirement cannot be applied directly to Δ because −I acts trivially. Lebesgue/Basic.lean, Lebesgue/Map.lean and Bochner/Set.lean supply countable additivity and change of variables. No relevant domain-transfer or equidecomposition declaration was found by the stated search in project/Definitions. Neither proposed name occurred in the searched DAG, node artifacts, Submission, or project snapshot. Both exact child types elaborated after import Submission, with exit code 0. Instance inspection confirmed hyperbolic volume and the canonical SL action through mapGL. The checked library results have only propext, Classical.choice and Quot.sound as transitive axioms. All nine dependency repositories were rechecked clean at their pinned revisions; referenced mathlib files and the recorded project import closure matched the snapshot.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/235

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
