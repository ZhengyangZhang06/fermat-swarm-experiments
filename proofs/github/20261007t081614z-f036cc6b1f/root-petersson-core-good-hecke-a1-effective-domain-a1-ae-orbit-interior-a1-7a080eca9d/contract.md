<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1 -->

## Theorem `Submission.f036cc6b1f_pc_ed_ae_orbit_interior`

Let G = SL₂(ℤ) act on the upper half-plane ℍ by Möbius transformations, and let μ = dx dy/y². Put F₀ = {z ∈ ℍ : 1 ≤ |z|² and |Re z| ≤ 1/2} and F₀° = {z ∈ ℍ : 1 < |z|² and |Re z| < 1/2}. For μ-almost every z ∈ ℍ, every a ∈ G satisfies: if az ∈ F₀, then az ∈ F₀°.

Node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/31

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/113, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/114

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_ed_ae_orbit_interior`

```lean
∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo
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
- Child DAG node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define E = F₀ \ F₀°. The defining functions z ↦ |z|² and z ↦ |Re z| are continuous. Thus F₀ is closed and F₀° is open in ℍ, so E is Borel measurable. These domain facts are also ModularGroup.isClosed_fd and ModularGroup.isOpen_fdo in the pinned Mathlib/NumberTheory/Modular.lean.
2. If z = x + iy belongs to E, then x² + y² ≥ 1 and |x| ≤ 1/2, but the two corresponding strict inequalities do not both hold. Consequently either x² + y² = 1 or |x| = 1/2. Therefore the image of E in ℂ lies in the union of the circle x² + y² = 1 and the two lines x = 1/2 and x = -1/2.
3. Each of these three sets has planar Lebesgue measure zero. Under ℂ ≅ ℝ × ℝ, a vertical line is {c} × ℝ, whose product measure is zero since a singleton has one-dimensional Lebesgue measure zero. The circle is closed, and its section at each fixed real coordinate x contains at most two imaginary coordinates y. Every such section has one-dimensional measure zero, so Tonelli's theorem applied to the circle's indicator gives planar measure zero. Their finite union is null, and hence the image of E is null.
4. The hyperbolic measure of a set is the integral of the density y⁻² over its image in ℂ. This is precisely UpperHalfPlane.volume_eq_lintegral in the pinned Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean. An integral over a planar null set is zero, so μ(E) = 0.
5. Fix a ∈ G. Its action is the restriction of the GL₂(ℝ) action through SpecialLinearGroup.mapGL, as defined by UpperHalfPlane.SLAction in the pinned Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean. The GL action preserves hyperbolic measure by the invariant-measure instance proved in Measure.lean. Each action map and its inverse are continuous by UpperHalfPlane.instContinuousGLSMul in Topology.lean. Thus Bₐ = {z ∈ ℍ : az ∈ E} is measurable and μ(Bₐ) = μ(E) = 0.
6. The group G is countable: its underlying matrices form a subset of the finite product of four copies of ℤ. Therefore N = ⋃ₐ∈G Bₐ is a countable union of measurable null sets and is itself measurable and null.
7. For z outside N and any a ∈ G, one has az ∉ E. If also az ∈ F₀, the identity E = F₀ \ F₀° implies az ∈ F₀°. The complement of N has full μ-measure, which proves the stated almost-everywhere assertion.

## Key steps

1. Express the closed-minus-open domain as a measurable subset of two vertical lines and a circle.
2. Prove planar nullness using product measure and Tonelli's theorem.
3. Transfer nullness to hyperbolic measure using its density formula.
4. Use invariant measure to show every modular preimage of the boundary is null.
5. Remove the countable union of those preimages to obtain the simultaneous assertion for every modular translate.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
