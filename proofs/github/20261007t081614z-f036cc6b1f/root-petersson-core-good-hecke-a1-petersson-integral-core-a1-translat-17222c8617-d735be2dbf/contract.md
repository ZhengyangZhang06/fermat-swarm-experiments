<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1.planar_exp_integrable_fd-a1 -->

## Theorem `Submission.f036cc6b1f_tdi_planar_exp_integrable_fd`

Let ℍ be the upper half-plane, F₀={z∈ℍ : 1≤|z|² and |Re z|≤1/2}, and ν=dx dy, the comap of complex Lebesgue measure along the inclusion ℍ→ℂ. For every real a>0, the real-valued function z↦exp(−a Im z) is ν-integrable on F₀.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1.planar_exp_integrable_fd-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/199

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_tdi_planar_exp_integrable_fd`

```lean
∀ (a : ℝ), 0 < a → MeasureTheory.IntegrableOn (fun z : UpperHalfPlane => Real.exp (-a * z.im)) ModularGroup.fd ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe)
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
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1.planar_exp_integrable_fd-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a>0 and let ν be the stated planar measure. Put b=√3/2>0. If z=x+iy belongs to F₀, then x²≤1/4 and x²+y²≥1. Therefore y²≥3/4, and y>0 gives y≥b. Consequently F₀ is contained in S={x+iy : −1/2≤x≤1/2, b≤y}. Both sets are Borel, since their defining coordinate and norm functions are continuous.
2. The inclusion ℍ→ℂ is a measurable embedding, as established by UpperHalfPlane.measurableEmbedding_coe. Since ν is its comap measure, integration on S agrees with integration over its image in ℂ. The volume-preserving coordinate identification Complex.volume_preserving_equiv_real_prod then identifies this measure with dx dy on [−1/2,1/2]×[b,∞).
3. For R≥b, the antiderivative −exp(−ay)/a gives the integral of exp(−ay) on [b,R] as (exp(−ab)−exp(−aR))/a. Because a>0, exp(−aR) tends to zero as R tends to infinity. Monotone convergence for the nonnegative integrand therefore gives its nonnegative Lebesgue integral on [b,∞) as exp(−ab)/a<∞; interval endpoints have measure zero. Tonelli's theorem now gives the nonnegative integral of exp(−a Im z) on S as exp(−ab)/a, since the horizontal interval has length one.
4. The function z↦exp(−a Im z) is continuous, hence strongly measurable, and nonnegative, so its norm equals itself. Its norm integral on F₀ is at most its finite integral on S. Strong measurability and finiteness of this norm integral prove the asserted real Bochner integrability.

## Key steps

1. Use the defining inequalities of F₀ to place it in a width-one strip above height √3/2.
2. Identify planar comap measure with product Lebesgue measure through the inclusion and complex coordinate equivalence.
3. Integrate the positive exponential on the strip using its antiderivative, monotone convergence, and Tonelli.
4. Restrict the finite norm integral to F₀ and conclude Bochner integrability.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/266

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
