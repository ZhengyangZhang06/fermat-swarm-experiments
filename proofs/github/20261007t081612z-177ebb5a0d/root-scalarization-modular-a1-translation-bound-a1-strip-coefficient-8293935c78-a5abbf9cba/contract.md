<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.polynomial_exponential_tail-a1 -->

## Theorem `Submission.p02_es_177ebb5a_scl_polynomial_exp_tail`

Let n∈ℕ and a∈ℝ with a>0. Define w(s)=(1+s)^n exp(−as) and J=∫_(0,∞) w(s) ds, using real Lebesgue measure. Then w is integrable on (0,∞), J≥0, and for all real 0≤y≤t one has ∫_y^t w(s) ds≤J(1+y)^n exp(−ay). Moreover w(y)→0 as y→+∞.

Node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.polynomial_exponential_tail-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/104

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_scl_polynomial_exp_tail`

```lean
∀ (n : ℕ) (a : ℝ), 0 < a → MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ n * Real.exp (-a * s)) (Set.Ioi 0) ∧ 0 ≤ (∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) ∧ (∀ (y t : ℝ), 0 ≤ y → y ≤ t → (∫ s in y..t, (1 + s) ^ n * Real.exp (-a * s)) ≤ (∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) * (1 + y) ^ n * Real.exp (-a * y)) ∧ Filter.Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-a * y)) Filter.atTop (nhds 0)
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

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.polynomial_exponential_tail-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Set w(s)=(1+s)^n exp(−as). This is continuous on ℝ and nonnegative for s≥0. For 0≤s≤1, (1+s)^n≤2^n≤2^n(1+s^n); for s≥1, (1+s)^n≤(2s)^n≤2^n(1+s^n). Thus this bound holds for every s≥0, also when n=0.
2. Since as/2≥0, the exponential series has nonnegative terms and gives exp(as/2)≥(as/2)^n/n!. Because a>0, multiplication by n!(2/a)^n yields s^n≤n!(2/a)^n exp(as/2). Therefore 0≤w(s)≤B exp(−as/2) for s≥0, where B=2^n(1+n!(2/a)^n). Here the constant term is bounded using exp(−as)≤exp(−as/2).
3. The function B exp(−as/2) has finite integral 2B/a on (0,∞), by its elementary antiderivative and exponential decay. Continuity makes w measurable, so comparison proves that w is integrable on (0,∞). Its integral J is nonnegative because w is nonnegative there.
4. Fix 0≤y≤t. The substitution s=y+v gives ∫_y^t w(s) ds=∫_0^(t−y) w(y+v) dv. For v≥0, 1+y+v≤(1+y)(1+v) and exp(−a(y+v))=exp(−ay)exp(−av), so w(y+v)≤w(y)w(v). Consequently the last integral is at most w(y)∫_0^(t−y)w(v)dv≤w(y)J. The final inequality uses nonnegativity and integrability on (0,∞); endpoints have Lebesgue measure zero. This is the stated tail estimate, including t=y.
5. For y≥1, (1+y)^n≤2^n y^n. The (n+1)-st term in the exponential series gives exp(ay)≥(ay)^(n+1)/(n+1)!. Since a,y>0, it follows that 0≤w(y)≤2^n(n+1)!/(a^(n+1)y). The last expression tends to zero, so the squeeze theorem proves w(y)→0. This argument includes n=0.

## Key steps

1. Dominate the polynomial factor using a term of the exponential series.
2. Compare with an integrable exponential to obtain a finite nonnegative J.
3. Translate a finite interval and use w(y+v)≤w(y)w(v) to bound its integral.
4. Use the (n+1)-st exponential term to bound w(y) by a constant divided by y.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|def linePow|abbrev BinaryForm|strip.*limit|coefficient.*limit`
- `integrable.*exp|tendsto.*exp|norm_sub_le_integral|finite_of_degree_eq|coeff.*pow`
- `tendsto_pow_mul_exp_neg_atTop_nhds_zero|tendsto_pow_mul_exp|finite_of_degree_eq|continuous.*coeff|ofComplex.*continuous|continuous.*ofComplex`
- `coeff_eq_zero|mem_homogeneousSubmodule|isHomogeneous_monomial|degree`
- `strip.*limit|limit.*strip|linePow.*(bound|norm)|norm.*linePow`
- `rg -n --hidden -g 'dag.json' -g 'decomposition-v*.json' -g '*handoff*.json' -g '*.lean' 'p02_es_177ebb5a_scl_(linepow_coeff_bound|polynomial_exp_tail|scalar_strip_limit)' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_scl_decomposition_types.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Coeff.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/ExpDecay.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DistLEIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Finsupp/Weight.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis`
- `/tmp/p02_scl_decomposition_types.lean`

Both reference snapshots are clean and match project revision 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib is clean at that revision, and the two relevant project definition files match the snapshot byte-for-byte. IsEichlerIntegral specifies coefficientwise complex derivatives; BinaryForm is the homogeneous polynomial submodule. Mathlib supplies multinomial coefficient formulas, exponential integrability and decay, segment norm estimates, finite degree-coordinate sets, and off-degree coefficient vanishing. The strip-limit/linePow-bound search returned no matches. All three proposed names were absent from the DAG and recorded handoffs/decompositions. All three exact types elaborate after import Submission. Transitive axiom checks for the seven inspected supporting declarations report only propext, Classical.choice, and Quot.sound. These are interface and reference checks, not comparator acceptance of any proposed child proof.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/192

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
