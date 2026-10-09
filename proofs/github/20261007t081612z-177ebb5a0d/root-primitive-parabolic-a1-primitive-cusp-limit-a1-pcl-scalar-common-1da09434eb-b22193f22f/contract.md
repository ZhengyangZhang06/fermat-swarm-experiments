<!-- theorem-id: fermat-p02/root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1 -->

## Theorem `Submission.p02_es_177ebb5a_pcl_scalar_common_ray_limit`

Let n∈ℕ, a>0, and H,G:ℂ→ℂ. Assume G is continuous on the open upper half-plane and H has complex derivative G(z) at every z with Im z>0. Assume that for every B>0 there exist real C≥0 and Y≥1 such that |G(z)|≤C(1+Im z)^n exp(−a Im z) whenever |Re z|≤B and Im z≥Y. Then there exists A∈ℂ such that, for every real x, H(x+iy) tends to A as the real variable y tends to +∞.

Node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/71

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/165, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/166

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_pcl_scalar_common_ray_limit`

```lean
∀ (n : ℕ) (a : ℝ) (H G : ℂ → ℂ), 0 < a → ContinuousOn G {z : ℂ | 0 < z.im} → (∀ z : ℂ, 0 < z.im → HasDerivAt H (G z) z) → (∀ B : ℝ, 0 < B → ∃ C Y : ℝ, 0 ≤ C ∧ 1 ≤ Y ∧ ∀ z : ℂ, |z.re| ≤ B → Y ≤ z.im → ‖G z‖ ≤ C * (1 + z.im) ^ n * Real.exp (-a * z.im)) → ∃ A : ℂ, ∀ x : ℝ, Filter.Tendsto (fun y : ℝ => H ((x : ℂ) + (y : ℂ) * Complex.I)) Filter.atTop (nhds A)
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

- Parent DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1`
- Child DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the hypotheses and write p(t)=(1+t)^n exp(−at) for t≥0. For every integer r≥0 and t>0, the exponential series gives exp(at)≥(at)^(r+1)/(r+1)!. Hence 0≤t^r exp(−at)≤(r+1)!/(a^(r+1)t), which tends to zero. Expanding (1+t)^n by the binomial theorem therefore proves p(t)→0 as t→+∞.
2. The function p is integrable on [0,∞). To establish this explicitly, set I_r(T)=∫₀ᵀ t^r exp(−at) dt for T≥0. Direct integration gives I_0(T)=(1−exp(−aT))/a. Integration by parts gives I_{r+1}(T)=−T^(r+1)exp(−aT)/a+((r+1)/a)I_r(T); the lower boundary term vanishes because r+1>0. The boundary limits from step 1 and induction imply I_r(T)→r!/a^(r+1). Each integrand is continuous and nonnegative, so monotone convergence on expanding finite intervals identifies this finite limit with its integral on [0,∞), proving integrability. A finite binomial expansion now gives J=∫₀∞p(t)dt=Σ_{r=0}^n binomial(n,r)r!/a^(r+1), and in particular 0≤J<∞.
3. If v≥y≥0, substitute t=y+s. Since 1+y+s≤(1+y)(1+s), nonnegativity and the exponential addition formula give ∫ᵧᵛp(t)dt≤p(y)∫₀^{v−y}p(s)ds≤Jp(y).
4. Apply the strip hypothesis with B=1, obtaining C₁≥0 and Y₁≥1. On the imaginary ray, the real-variable function h(t)=H(it) has derivative iG(it) for t>0, by the chain rule and restriction of the complex derivative to real parameters. This derivative is continuous on every compact interval in (0,∞), by continuity of G. Thus for v≥y≥Y₁, the fundamental theorem of calculus and |i|=1 give |H(iv)−H(iy)|≤∫ᵧᵛ|G(it)|dt≤C₁∫ᵧᵛp(t)dt≤C₁Jp(y).
5. Given ε>0, step 1 supplies T≥Y₁ such that C₁Jp(t)<ε for every t≥T. For arbitrary u,v≥T, apply step 4 with the smaller argument first and use symmetry of distance. It follows that |H(iu)−H(iv)|<ε. This is the Cauchy criterion at infinity, so completeness of ℂ supplies A∈ℂ with H(iy)→A as y→+∞.
6. Fix any real x and choose B=|x|+1. Obtain C_B≥0 and Y_B≥1 from the corresponding strip hypothesis. For y≥Y_B, parameterize the horizontal segment by z(s)=sx+iy, 0≤s≤1. Its points satisfy |Re z(s)|≤|x|<B and Im z(s)=y>0. The real derivative of s↦H(z(s)) is xG(z(s)), and it is continuous. The fundamental theorem of calculus therefore gives |H(x+iy)−H(iy)|≤∫₀¹|x||G(sx+iy)|ds≤|x|C_Bp(y). This also holds for negative x and for x=0.
7. By step 1 the last bound tends to zero. Combining it with H(iy)→A gives H(x+iy)→A. The number A was fixed using only the imaginary ray before x was chosen, so it works for every real x. All estimates hold eventually as y→+∞; no assumption on H or G in the lower half-plane is needed.

## Key steps

1. Prove decay of the polynomial–exponential weight using the exponential series.
2. Establish its finite integral through integration by parts and moment induction.
3. Bound every finite tail integral by J times the weight at its starting point.
4. Use vertical integration to prove the Cauchy criterion and obtain a complex limit.
5. Use horizontal integration to show every fixed vertical ray has that same limit.

## Reference use

### local-project

Queries:
- `scaled_cusp_decay|IsEichlerIntegral|binaryFormRepSL|eichlerShimuraMap_injective`
- `hasDerivAt|ofComplex|coe_specialLinearGroup_apply`
- `integrableOn.*exp|integrableOn.*rpow|tendsto.*exp.*atTop`
- `sum_monomial_eq|coeff_sum|coeff_smul|coeff_monomial|coeff_mul_X|coeff_add`
- `scaled_cusp_decay|common_ray_limit|linear_linepow_growth`
- `sed -n '35,135p' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_pcl_decomposition_checks/Check.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The installed mathlib HEAD matches and has no tracked modifications; both inspected HeckeEis definition files match the snapshot byte-for-byte. The snapshot supplies coefficientwise IsEichlerIntegral, binaryFormRepSL_linePow, jFactor_ne_zero, the local ofComplex identities, the Möbius derivative, coefficient linearity, homogeneous support, exponential asymptotics, and the fundamental theorem of calculus. Searching the snapshot for scaled_cusp_decay|common_ray_limit|linear_linepow_growth returned no matches; scaled_cusp_decay is an existing parent DAG dependency. All three proposed types elaborated after import Submission. Transitive axiom checks of binaryFormRepSL_linePow, jFactor_ne_zero, hasStrictDerivAt_smul, integral_eq_sub_of_hasDerivAt, and tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero returned only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/227

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
