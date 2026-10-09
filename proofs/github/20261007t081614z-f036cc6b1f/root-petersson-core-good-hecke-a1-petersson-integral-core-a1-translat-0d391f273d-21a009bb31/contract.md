<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1.petersson_integrable_of_exp_product-a1 -->

## Theorem `Submission.f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound`

Let u,v:ℍ→ℂ be continuous. Let a,C,Y∈ℝ satisfy a>0 and C≥0, and assume that ‖u(z)v(z)‖≤C exp(−a Im z) for every z∈ℍ with Y≤Im z. Put F₀={z∈ℍ : 1≤|z|² and |Re z|≤1/2} and μ=dx dy/y². Then z↦conjugate(u(z))v(z)(Im z)² is μ-integrable on F₀.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1.petersson_integrable_of_exp_product-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/199

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/209

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound`

```lean
∀ (u v : UpperHalfPlane → ℂ) (a C Y : ℝ), Continuous u → Continuous v → 0 < a → 0 ≤ C → (∀ z : UpperHalfPlane, Y ≤ z.im → ‖u z * v z‖ ≤ C * Real.exp (-a * z.im)) → MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v) ModularGroup.fd (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)
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

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1.petersson_integrable_of_exp_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix u,v,a,C,Y satisfying the hypotheses. Write ν=dx dy for planar measure on ℍ and μ=dx dy/y². Put L=max 1 Y, D=F₀∩{Im z≤L}, and E=F₀∩{L<Im z}. These sets are Borel, are disjoint, and have union F₀. All norm integrals below are nonnegative Lebesgue integrals, so their use does not presuppose Bochner integrability.
2. Put b=√3/2. For z=x+iy in F₀, the inequalities x²≤1/4 and x²+y²≥1 imply y≥b>0. Thus D is a closed subset of the compact rectangle [−1/2,1/2]×[b,L], which lies entirely inside ℍ. Consequently D is compact and has finite planar measure, bounded by the rectangle's finite area. The function W(z)=conjugate(u(z))v(z) is continuous. Compactness supplies B≥0 bounding ‖W‖ on D, so the norm integral of W on D is at most Bν(D)<∞.
3. Apply the sibling planar_exp_integrable_fd with the given a>0. It supplies ν-integrability of z↦exp(−a Im z) on F₀. If z∈E, then Im z>L≥Y, and the norm identities for conjugation and multiplication give ‖W(z)‖=‖u(z)v(z)‖≤C exp(−a Im z). Since C≥0, this is a nonnegative integrable majorant on E. Hence the norm integral of W on E is finite. Additivity over the disjoint Borel partition D∪E=F₀ proves that the norm integral of W on F₀ is finite.
4. Define P(z)=W(z)(Im z)², which equals UpperHalfPlane.petersson 2 u v z. By UpperHalfPlane.volume_def, μ is ν with density (Im z)⁻². For every z∈ℍ, Im z>0, and therefore ‖P(z)‖(Im z)⁻²=‖W(z)‖. The with-density formula after restriction to the Borel set F₀ identifies the μ-norm integral of P with the finite ν-norm integral of W established in step 3.
5. The function P is continuous because u,v and Im are continuous. It is therefore strongly measurable with values in the separable space ℂ. Together with the finite μ-norm integral from step 4, this proves its complex Bochner integrability on F₀.

## Key steps

1. Partition F₀ into a lower truncation and a tail above max 1 Y.
2. Use the positive height lower bound and continuity to obtain a finite planar norm integral on the compact truncation.
3. Apply planar_exp_integrable_fd and the product bound to control the tail.
4. Cancel the weight y² against the hyperbolic density y⁻² in the norm integral.
5. Combine continuity with the finite norm integral to conclude Petersson integrability.

## Reference use

### local-project

Queries:
- `petersson_slash_SL|exp_decay_atImInfty|zero_at_infty_slash|integrable.*petersson|petersson.*integrable`
- `im.*fd|fd.*im|def fd|isCompact_truncated|isClosed_fd`
- `integrable.*exp|integral.*exp`
- `integrable_withDensity|lintegral_withDensity|integrableOn_iff_comap`
- `integrableOn_comp_preimage|integrableOn_image|integrableOn.*smul|integrableOn_comp_iff`
- `petersson.*integrable|integrable.*petersson|planar_exp_integrable_fd|petersson_integrable_of_exp_product_bound`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Integral/ExpDecay.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Basic and QExpansion provide translated cusp conditions and exponential decay; Petersson provides slash covariance. Modular provides the height lower bound and compact truncated domains. Measure identifies hyperbolic volume as planar comap measure with density y⁻² and proves action invariance. ExpDecay, Lebesgue/Complex, and the integration files provide exponential integrability, volume-preserving coordinates, density conversion, and image transport. The direct Petersson-integrability search found no matching theorem. All nine dependency checkouts matched their pins and were clean; inspected sources matched the snapshot. Audited library declarations had only propext, Classical.choice, and Quot.sound as transitive axioms.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/411

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
