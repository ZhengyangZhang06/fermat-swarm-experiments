<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1.ssl_segment_estimates-a1 -->

## Theorem `Submission.p02_es_177ebb5a_ssl_segment_estimates`

Let L,y₀∈ℝ satisfy L≥0 and y₀>0. Let F,H:ℂ→ℂ and w:ℝ→ℝ. Suppose H is continuous on {z:Im z>0}, F has complex derivative H(z) at every point of that half-plane, w is continuous on [y₀,∞), and ‖H(z)‖≤w(Im z) whenever 0≤Re z≤L and Im z≥y₀. Then: (i) for every x,y,t∈ℝ with 0≤x≤L and y₀≤y≤t, ‖F(x+it)−F(x+iy)‖≤∫_y^t w(s)ds; and (ii) for every x,y∈ℝ with 0≤x≤L and y≥y₀, ‖F(x+iy)−F(iy)‖≤xw(y). All integrals use real Lebesgue measure.

Node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1.ssl_segment_estimates-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/128

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_ssl_segment_estimates`

```lean
∀ (F H : ℂ → ℂ) (w : ℝ → ℝ) (L y₀ : ℝ), 0 ≤ L → 0 < y₀ → ContinuousOn H {z : ℂ | 0 < z.im} → (∀ z : ℂ, 0 < z.im → HasDerivAt F (H z) z) → ContinuousOn w (Set.Ici y₀) → (∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im → ‖H z‖ ≤ w z.im) → (∀ (x y t : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y → y ≤ t → ‖F ((x : ℂ) + (t : ℂ) * Complex.I) - F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ∫ s in y..t, w s) ∧ (∀ (x y : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y → ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((y : ℂ) * Complex.I)‖ ≤ x * w y)
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

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1.ssl_segment_estimates-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. For every height u≥y₀, the point iu belongs to the strip because L≥0. The derivative bound gives 0≤‖H(iu)‖≤w(u). Thus w is nonnegative at all relevant heights.
2. Fix x,y,t satisfying 0≤x≤L and y₀≤y≤t. For s∈[y,t], the point φ(s)=x+is lies in the strip and in the open upper half-plane: Im φ(s)=s≥y₀>0. Restrict the complex derivative of F to real scalars and apply the real chain rule. The real-variable function g(s)=F(x+is) has derivative g′(s)=H(x+is)i at every s∈[y,t].
3. Continuity of H on the upper half-plane and continuity of φ imply continuity of s↦H(x+is)i on [y,t]. Consequently this derivative is interval integrable. The fundamental theorem of calculus yields F(x+it)−F(x+iy)=∫_y^t H(x+is)i ds.
4. The restriction of w to [y,t] is continuous, hence interval integrable. For each s in this interval, ‖H(x+is)i‖=‖H(x+is)‖≤w(s), since ‖i‖=1. Taking the norm of the integral and integrating this pointwise bound gives ‖F(x+it)−F(x+iy)‖≤∫_y^t w(s)ds. This proves (i).
5. Now fix x,y satisfying 0≤x≤L and y≥y₀. For s∈[0,x], the point ψ(s)=s+iy lies in the strip and in the upper half-plane. The same real chain rule gives the derivative H(s+iy) for the function h(s)=F(s+iy). This derivative is continuous on [0,x], so the fundamental theorem gives F(x+iy)−F(iy)=∫_0^x H(s+iy)ds.
6. On [0,x], the hypothesis gives ‖H(s+iy)‖≤w(y). The norm-integral inequality therefore yields ‖F(x+iy)−F(iy)‖≤∫_0^x w(y)ds=xw(y), proving (ii). When t=y or x=0, the respective integral and difference are both zero, so these endpoint cases are included.

## Key steps

1. Place both segments inside the strip and the open upper half-plane.
2. Restrict complex derivatives to real scalars and apply the chain rule along the vertical segment.
3. Use continuity of the derivative, the fundamental theorem of calculus, and the weight bound to obtain the vertical integral estimate.
4. Apply the same argument along the horizontal segment, whose derivative bound is constant.
5. Evaluate the constant integral as xw(y), including zero-length segments.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `rg -n 'scalar_strip_limit|strip_segment_bounds|tail_modulus_limit|polynomial_exp_tail' project`
- `rg -n 'integral_eq_sub_of_hasDerivAt|norm_integral_le_of_norm_le|complexToReal_fderiv|cauchySeq_iff|cauchySeq_tendsto_of_complete' mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean mathlib/Mathlib/Analysis/Complex/RealDeriv.lean mathlib/Mathlib/Topology/MetricSpace/Cauchy.lean mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `rg -n 'p02_es_177ebb5a_ssl_segment_estimates|p02_es_177ebb5a_ssl_tail_limit' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes Submission.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_ssl_decomposition_typecheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/RealDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Topology/MetricSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/tmp/p02_ssl_decomposition_typecheck.lean`

The snapshot-relative rg commands ran from the specified snapshot root. Its project search found no matches for the four requested strip-limit or weight-lemma identifiers. The inspected mathlib files provide restriction of complex derivatives to real derivatives, the vector-valued fundamental theorem of calculus, norm-integral bounds, a Cauchy criterion allowing real indices, and convergence by completeness. The manifest records project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; the installed mathlib HEAD matches and its working tree is clean. Both proposed types successfully elaborated after import Submission with Lean 4.33.1. Transitive axiom queries for the six cited library declarations returned only propext, Classical.choice, and Quot.sound. Both proposed names were absent from the active DAG and searched declarations. These checks validate the interfaces and library references, not acceptance of unimplemented child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/340

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
