<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.effective_domain-a1.transversal_unique_mod_sign-a1 -->

## Theorem `Submission.f036cc6b1f_pc_ed_transversal_unique`

Let G = SL₂(ℤ), and define F₀ = {z ∈ ℍ : 1 ≤ |z|² and |Re z| ≤ 1/2} and F₀° = {z ∈ ℍ : 1 < |z|² and |Re z| < 1/2}. Let Δ ≤ G and let R ⊂ G be finite. Assume -I ∈ Δ and that, for every r,s ∈ R, membership sr⁻¹ ∈ Δ implies s = r. Let z ∈ ℍ satisfy az ∈ F₀ ⇒ az ∈ F₀° for every a ∈ G, and put F = ⋃ᵣ∈R rF₀. For every γ,δ ∈ Δ such that γz ∈ F and δz ∈ F, one has δ = γ or δ = -γ. Neither finite index nor coverage by R is assumed.

Node: `root.petersson_core_good_hecke-a1.effective_domain-a1.transversal_unique_mod_sign-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/31

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_ed_transversal_unique`

```lean
∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)), (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) → ∀ z : UpperHalfPlane, (∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo) → let F : Set UpperHalfPlane := ⋃ r ∈ R, (fun w : UpperHalfPlane => r • w) '' ModularGroup.fd; ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ → δ ∈ Δ → γ • z ∈ F → δ • z ∈ F → δ = γ ∨ δ = -γ
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

- Parent DAG node: `root.petersson_core_good_hecke-a1.effective_domain-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.effective_domain-a1.transversal_unique_mod_sign-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Δ, R, z, γ, and δ satisfying all the hypotheses. From membership in F, choose r,s ∈ R and w,v ∈ F₀ such that γz = rw and δz = sv.
2. The action law gives (r⁻¹γ)z = w. Apply the assumed property of z to a = r⁻¹γ. Since w ∈ F₀, this gives w ∈ F₀°.
3. Define a = s⁻¹δγ⁻¹r ∈ G. The action law and the chosen identities give aw = s⁻¹δγ⁻¹(rw) = s⁻¹δγ⁻¹(γz) = s⁻¹δz = v. Hence w ∈ F₀° and aw ∈ F₀. By ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd in the pinned Mathlib/NumberTheory/Modular.lean, a = I or a = -I.
4. Put q = δγ⁻¹. Since γ,δ ∈ Δ and Δ is a subgroup, q ∈ Δ. Rearranging the definition of a yields q = sar⁻¹. If a = I, then q = sr⁻¹, so sr⁻¹ ∈ Δ. If a = -I, the centrality of -I gives q = (-I)sr⁻¹. Multiplying by -I on the left and using (-I)² = I gives sr⁻¹ = (-I)q ∈ Δ, because both -I and q belong to Δ.
5. In either case, r,s ∈ R and sr⁻¹ ∈ Δ. The separation hypothesis on R therefore gives s = r. Substituting into q = sar⁻¹, and using a = I or a = -I together with centrality of -I, gives q = I or q = -I.
6. Multiply q = δγ⁻¹ on the right by γ. If q = I this yields δ = γ; if q = -I this yields δ = (-I)γ = -γ. This proves the required disjunction.

## Key steps

1. Choose standard-domain points witnessing the two translated-domain memberships.
2. Use the orbit hypothesis to put the first witness in the open standard domain.
3. Apply modular interior uniqueness to s⁻¹δγ⁻¹r.
4. Use containment of -I in Δ to deduce sr⁻¹ ∈ Δ in both sign cases.
5. Apply separation of right-coset representatives and cancel γ to obtain uniqueness modulo sign.

## Reference use

### local-project

Queries:
- `exists_smul_mem_fd|eq_one_or_neg_one_of_mem_fdo_mem_fd|def fdo|def fd|isClosed_fd|isOpen_fdo`
- `volume.*(ModularGroup\.)?(fd|fdo)|(fd|fdo).*volume|measure.*(fd|fdo)|(fd|fdo).*measure`
- `volume_eq_lintegral|instMeasureSpace|SMulInvariantMeasure|volume_aux|SLAction|mapGL|instContinuousGLSMul|smul_eq`
- `measure_prod_null_of_ae_null|theorem lintegral_prod|volume_preserving_equiv_real_prod`
- `f036cc6b1f_pc_ed_ae_orbit_interior|f036cc6b1f_pc_ed_transversal_unique`
- `instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions|coe_rescaleLin_apply|instIsOpenPosMeasureUpperHalfPlaneVolume_definitions|nontrivial_gamma0L2|unipotentDiagonalSum_zero`
- `git -C .lake/packages/mathlib status --porcelain`
- `#synth MeasureTheory.MeasureSpace UpperHalfPlane`
- `#synth SMul (Matrix.SpecialLinearGroup (Fin 2) ℤ) UpperHalfPlane`
- `#synth Neg (Matrix.SpecialLinearGroup (Fin 2) ℤ)`
- `#print axioms ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd`
- `#print axioms UpperHalfPlane.instSMulInvariantMeasureGeneralLinearGroupFinOfNatNatRealVolume`
- `#print axioms CuspForm.heckeTLin`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1/compatibility-v2/Compatibility.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1/compatibility-v2/AttributeTargets.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1/compatibility-v2/SubmissionBuild.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1/compatibility-v2/SubmissionBuild.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1/compatibility-v2/ImportSubmissionCheck.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1/compatibility-v2/ImportSubmissionCheck.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1/compatibility-v2/Summary.json`

The snapshot pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. All nine installed dependencies match their pinned revisions and are clean; all 20 reused project dependency sources and six inspected mathlib sources match the snapshot. Modular.lean supplies covering, interior uniqueness modulo sign, and domain topology. Measure.lean supplies hyperbolic volume and GL invariance; Topology.lean and MoebiusAction.lean justify the continuous restricted SL action. The targeted boundary-measure search found no relevant fd/fdo nullness lemma. Neither proposed identifier is reserved in the DAG or declared in Submission or the reference project. Lean confirmed that all 15 targets of the failing attribute-removal commands are absent. Those commands were retained as comments in Submission.lean, preserving its imports and theorem declaration and leaving the frozen problem and dependencies unchanged. The repaired Submission build exited 0, and both unchanged frozen expressions successfully elaborated as Prop through literal import Submission. Instance checks confirmed UpperHalfPlane.instMeasureSpace, UpperHalfPlane.SLAction.toSMul, and Matrix.SpecialLinearGroup.instNeg. Thirteen audited infrastructure declarations use only propext, Classical.choice, and Quot.sound. The build retains the pre-existing unfinished-root warning; these checks establish compatibility, not theorem acceptance. No children were activated.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/336

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
