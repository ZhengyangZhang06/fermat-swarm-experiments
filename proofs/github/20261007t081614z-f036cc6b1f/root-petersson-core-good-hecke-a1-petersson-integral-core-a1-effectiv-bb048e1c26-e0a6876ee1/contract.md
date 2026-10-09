<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1 -->

## Theorem `Submission.f036cc6b1f_pic_dt_measurable_equidecomposition`

Let G = SL₂(ℤ) act canonically on the upper half-plane ℍ, with hyperbolic measure μ = dx dy/y². Let Δ ≤ G contain −I, and let E,F ⊆ ℍ be measurable. For each S ∈ {E,F}, assume that for μ-almost every z there exists γ ∈ Δ such that γz ∈ S and every δ ∈ Δ with δz ∈ S satisfies δ = γ or δ = −γ. Then there exist families A,B : Δ → Set ℍ such that every Aγ and Bγ is measurable, each family is pairwise disjoint, E agrees μ-almost everywhere with ⋃γ Aγ, F agrees μ-almost everywhere with ⋃γ Bγ, and the image of Aγ under z ↦ γ⁻¹z is exactly Bγ for every γ ∈ Δ.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/200

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/217, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/218

## Lean problem

Declaration: `Submission.f036cc6b1f_pic_dt_measurable_equidecomposition`

```lean
∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F : Set UpperHalfPlane), (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → MeasurableSet E → MeasurableSet F → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ) → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) → ∃ A B : Δ → Set UpperHalfPlane, (∀ γ, MeasurableSet (A γ)) ∧ (∀ γ, MeasurableSet (B γ)) ∧ Pairwise (fun γ δ => Disjoint (A γ) (A δ)) ∧ Pairwise (fun γ δ => Disjoint (B γ) (B δ)) ∧ (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ E ↔ z ∈ ⋃ γ, A γ) ∧ (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ F ↔ z ∈ ⋃ γ, B γ) ∧ (∀ γ : Δ, (fun z : UpperHalfPlane => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z) '' A γ = B γ)
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
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Δ,E,F satisfying the hypotheses, and write G = SL₂(ℤ). An element of G is determined by its four integer entries, so G and its subtype Δ are countable. For g ∈ G, the action map z ↦ gz equals the action of mapGL ℝ g. The pinned GL action is continuous and preserves hyperbolic volume; applying continuity also to g⁻¹ shows that this map is a measure-preserving homeomorphism. Furthermore, ModularGroup.SL_neg_smul gives (−g)z = gz.
2. For S = E or F, let R_S(z) mean that some γ ∈ Δ sends z into S and every δ ∈ Δ sending z into S equals γ or −γ. For fixed γ, the set of z with γz ∈ S is measurable. The membership and matrix-equality conditions involving γ and δ but not z are constant predicates. Countable unions and intersections over G therefore show that {z : R_S(z)} is measurable. Consequently N = {z : ¬R_E(z) or ¬R_F(z)} is measurable. Each exceptional set is null by its almost-everywhere hypothesis, so μ(N) = 0.
3. Define N* = ⋃δ∈Δ {z : δz ∈ N}, and X = ℍ \ N*. Every set in this countable union is a measurable preimage of N and has measure zero by measure preservation. Thus N* is measurable and null, while X is measurable and conull. Since the identity belongs to Δ, N ⊆ N*, and hence R_E(z) and R_F(z) hold for every z ∈ X.
4. The set X is Δ-invariant. Indeed, if z ∈ X and η ∈ Δ, then for every δ ∈ Δ the element δη belongs to Δ, so δ(ηz) = (δη)z does not belong to N. Therefore ηz ∈ X. Applying this implication to η⁻¹ also gives ηz ∈ X ⇒ z ∈ X.
5. At any z ∈ X, if p,q ∈ Δ both send z into the same S ∈ {E,F}, then q = p or q = −p. To see this, choose the witness r in R_S(z). Each of p and q equals r or −r. The four possibilities give either equality or opposition, using −(−r) = r.
6. Negation preserves Δ, since −p = (−I)p and −I ∈ Δ. The relation p ∼ q defined by q = p or q = −p is an equivalence relation: reflexivity is equality, symmetry follows by negating an equality when necessary, and transitivity follows by multiplying the two signs. Choose one representative from each equivalence class and let L ⊆ Δ be their set. Thus every p ∈ Δ equals γ or −γ for some γ ∈ L, and two members of L differing by sign are equal. The set L is countable as a subset of Δ. Since −I is central and has square I, (−p)⁻¹ = −p⁻¹.
7. Define families indexed by all γ ∈ Δ. For γ ∈ L put Aγ = E ∩ X ∩ γF and Bγ = F ∩ X ∩ γ⁻¹E, where group elements act on sets by image. For γ ∉ L put Aγ = Bγ = ∅. The images γF and γ⁻¹E are measurable because the action maps are homeomorphisms with measurable inverses. Hence every Aγ and Bγ is measurable.
8. The Aγ cover E ∩ X. For z ∈ E ∩ X, R_F(z) supplies δ ∈ Δ with δz ∈ F. Choose γ ∈ L representing the sign class of δ⁻¹. Then γ(δz) = z, since replacing a matrix by its negative does not change its action. Thus z ∈ γF and z ∈ Aγ. Conversely every Aγ lies in E ∩ X. They are pairwise disjoint: if z ∈ Aγ ∩ Aη, then both indices lie in L and γ⁻¹z,η⁻¹z ∈ F. Step 5 gives η⁻¹ = γ⁻¹ or η⁻¹ = −γ⁻¹. Inversion and the identity at the end of step 6 give η = γ or η = −γ. The defining property of L forces η = γ.
9. The Bγ cover F ∩ X. For z ∈ F ∩ X, choose δ ∈ Δ with δz ∈ E using R_E(z), and choose γ ∈ L representing δ modulo sign. Then γz = δz ∈ E, so z ∈ γ⁻¹E and z ∈ Bγ. Conversely every Bγ lies in F ∩ X. If z ∈ Bγ ∩ Bη, both indices lie in L and γz,ηz ∈ E. Step 5 gives η = γ or η = −γ, so η = γ. This proves pairwise disjointness.
10. Fix γ ∈ L. If z ∈ Aγ and y = γ⁻¹z, then y ∈ F because z ∈ γF, y ∈ X by step 4, and γy = z ∈ E. Thus y ∈ Bγ. Conversely, if y ∈ Bγ, put z = γy. Then z ∈ E, z ∈ X by step 4, and z ∈ γF because y ∈ F; hence z ∈ Aγ and γ⁻¹z = y. Therefore γ⁻¹Aγ = Bγ. For γ ∉ L this equality holds because both sets are empty. Finally, steps 8 and 9 identify the unions with E ∩ X and F ∩ X. Since X is conull, these unions agree almost everywhere with E and F, respectively. All asserted properties follow.

## Key steps

1. Use countability and the canonical measure-preserving homeomorphisms to make the representative predicates measurable.
2. Saturate their null exceptional set under Δ to obtain an invariant measurable conull set X.
3. Choose one representative of each sign class in Δ.
4. Define paired intersection pieces on those representatives and empty pieces at all other indices.
5. Prove coverage and pairwise disjointness using representative uniqueness modulo sign.
6. Prove inverse action maps each source piece exactly onto its paired target piece, then remove the null complement of X.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/537

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
