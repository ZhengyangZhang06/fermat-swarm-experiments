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
