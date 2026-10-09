<!-- theorem-id: fermat-p02/root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1.crl_imaginary_ray_limit-a1 -->

## Theorem `Submission.p02_es_177ebb5a_crl_imaginary_ray_limit`

Let n∈ℕ, a∈ℝ with a>0, and H,G:ℂ→ℂ. Suppose G is continuous on {z∈ℂ : Im z>0}, and H has complex derivative G(z) at every point of that set. Suppose there exist real C≥0 and Y≥1 such that ‖G(it)‖≤C(1+t)^n exp(−at) for every real t≥Y. Then there exists A∈ℂ such that H(iy)→A as the real variable y→+∞.

Node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1.crl_imaginary_ray_limit-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/163

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_crl_imaginary_ray_limit`

```lean
∀ (n : ℕ) (a : ℝ) (H G : ℂ → ℂ), 0 < a → ContinuousOn G {z : ℂ | 0 < z.im} → (∀ z : ℂ, 0 < z.im → HasDerivAt H (G z) z) → (∃ C Y : ℝ, 0 ≤ C ∧ 1 ≤ Y ∧ ∀ t : ℝ, Y ≤ t → ‖G ((t : ℂ) * Complex.I)‖ ≤ C * (1 + t) ^ n * Real.exp (-a * t)) → ∃ A : ℂ, Filter.Tendsto (fun y : ℝ => H ((y : ℂ) * Complex.I)) Filter.atTop (nhds A)
```

### Frozen project context

`Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean` at `1f74c284b125d4c45f527f2d621597fcf1e103a9` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HeckeEis_eichlerShimuraMap_injective.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_injective (N : ℕ) [NeZero N] (n : ℕ) :
    Function.Injective
      (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f) := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1`
- Child DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1.crl_imaginary_ray_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the hypotheses and choose C≥0 and Y≥1 witnessing the ray estimate. Write p(t)=(1+t)^n exp(−at) for t≥0. For every integer r≥0 and t>0, positivity of the exponential-series terms gives exp(at)≥(at)^(r+1)/(r+1)!. Consequently 0≤t^r exp(−at)≤(r+1)!/(a^(r+1)t). The upper bound tends to zero. The binomial expansion (1+t)^n=Σ_{r=0}^n binomial(n,r)t^r therefore shows that p(t)→0.
2. For r≥0 and T≥0, put I_r(T)=∫₀ᵀ t^r exp(−at) dt. Direct integration yields I_0(T)=(1−exp(−aT))/a. Integration by parts gives I_{r+1}(T)=−T^(r+1)exp(−aT)/a+((r+1)/a)I_r(T); the lower boundary term is zero. Step 1 makes the upper boundary term tend to zero. Induction on r now gives I_r(T)→r!/a^(r+1).
3. Each moment integrand is continuous and nonnegative on [0,∞). Apply monotone convergence to its restrictions to [0,k], k∈ℕ. Step 2 identifies the resulting integral on [0,∞) with the finite number r!/a^(r+1); hence each moment is integrable there. Taking the finite binomial sum proves integrability of p and gives J=∫₀∞p(t)dt=Σ_{r=0}^n binomial(n,r)r!/a^(r+1). In particular J is a finite nonnegative real number.
4. Let 0≤y≤v. Substituting t=y+s in the interval integral, use 1+y+s≤(1+y)(1+s) for s≥0 and exp(−a(y+s))=exp(−ay)exp(−as). All factors are nonnegative, so p(y+s)≤p(y)p(s). Thus ∫ᵧᵛp(t)dt≤p(y)∫₀^{v−y}p(s)ds≤Jp(y), where the final inequality follows from nonnegativity and integrability of p.
5. Set h(t)=H(it). For t>0, restricting the complex derivative of H to the real parameter t and applying the chain rule gives h′(t)=iG(it). For v≥y≥Y, all points it with t∈[y,v] lie in the open upper half-plane. Continuity of G there makes t↦iG(it) continuous on this compact interval, hence integrable. The fundamental theorem of calculus and ‖i‖=1 give ‖h(v)−h(y)‖≤∫ᵧᵛ‖G(it)‖dt≤C∫ᵧᵛp(t)dt≤CJp(y).
6. Given ε>0, step 1 and finiteness of C and J provide T≥Y such that CJp(t)<ε for every t≥T. For arbitrary u,v≥T, apply step 5 with the smaller argument first and use symmetry of the norm of a difference. It follows that ‖h(u)−h(v)‖<ε. In particular the sequence h(Y+k), k∈ℕ, is Cauchy, and completeness of ℂ supplies its limit A∈ℂ.
7. To prove convergence for all real y, fix ε>0 and choose T≥Y so that the bound in step 6 holds with ε/2. Choose k large enough that Y+k≥T and ‖h(Y+k)−A‖<ε/2. For every real y≥T, the triangle inequality gives ‖h(y)−A‖≤‖h(y)−h(Y+k)‖+‖h(Y+k)−A‖<ε. Hence H(iy)=h(y) tends to A as y→+∞.

## Key steps

1. Use the exponential series and binomial expansion to prove decay of the weight.
2. Compute exponential moments by integration by parts and identify their finite integrals by monotone convergence.
3. Bound finite tail integrals by J times the weight at the starting point.
4. Restrict the complex derivative to the imaginary ray and apply FTC.
5. Establish the Cauchy criterion at infinity and obtain a complex limit.
6. Extend convergence of an integer-spaced sequence to all real heights.

## Reference use

### local-project

Queries:
- `eichlerShimuraMap_injective|primitive.*limit|common_ray_limit|integrable.*exp|tendsto.*exp`
- `integrableOn.*exp|integrable.*mul_exp|tendsto.*pow.*exp|integral_eq_sub_of_hasDerivAt|norm_sub_le_integral|cauchy.*atTop|tendsto.*integrable`
- `tendsto.*[Dd]eriv.*[Ii]ntegrable|[Ii]ntegrable.*[Dd]eriv.*tendsto|tendsto.*integrableOn_Ioi|tendsto.*integral_Ioi`
- `integral_eq_sub_of_hasDerivAt|norm_integral_le_integral_norm`
- `p02_es_177ebb5a_crl_`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_crl_decomposition_checks/Types.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/ExpDecay.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/tmp/p02_crl_decomposition_checks/Types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The project search found the frozen injectivity declaration but no matching primitive-limit or exponential-integrability result. Pinned mathlib supplies exponential asymptotics, exponential integrability, convergence from an integrable derivative, FTC, and integral norm bounds. The installed mathlib revision matches, has no tracked modifications, and the five relevant inspected mathlib files match the snapshot byte-for-byte. Both proposed types successfully elaborated after import Submission. Transitive axiom checks of the seven inspected analysis declarations returned only propext, Classical.choice, and Quot.sound. Neither proposed name was reserved in the DAG. These checks validate the interfaces and library infrastructure, not acceptance of the proposed child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/190

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
