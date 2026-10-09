<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.translation_bound-a1.periodic_strip_bound-a1 -->

## Theorem `Submission.p02_es_177ebb5a_tb_periodic_strip_bound`

Let N∈ℕ with N≠0 and q:ℍ→ℂ. Assume q(T^Nτ)=q(τ) for every τ∈ℍ, where T=(1 1;0 1). Suppose there exist M,Y∈ℝ such that |q(τ)|≤M whenever 0≤Re τ≤N and Im τ≥Y. Then q is bounded at imaginary infinity in the sense of UpperHalfPlane.IsBoundedAtImInfty.

Node: `root.scalarization_modular-a1.translation_bound-a1.periodic_strip_bound-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/48

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_tb_periodic_strip_bound`

```lean
∀ (N : ℕ) [NeZero N] (q : UpperHalfPlane → ℂ), (∀ τ : UpperHalfPlane, q ((ModularGroup.T ^ N) • τ) = q τ) → (∃ M Y : ℝ, ∀ τ : UpperHalfPlane, 0 ≤ τ.re → τ.re ≤ (N : ℝ) → Y ≤ τ.im → ‖q τ‖ ≤ M) → UpperHalfPlane.IsBoundedAtImInfty q
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

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.periodic_strip_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix witnesses M and Y for the strip bound. Since N is a nonzero natural number, its real value is positive. Put g=T^N. The modular translation formula says that g acts by τ↦τ+N, preserving the imaginary part.
2. The assumed identity q(gτ)=q(τ) implies invariance under every nonnegative power of g by induction. Apply the same identity at g⁻¹τ to obtain q(τ)=q(g⁻¹τ), hence also invariance under g⁻¹. Induction using this inverse identity proves q(g^kτ)=q(τ) for every integer k.
3. Let τ=x+iy be any point of ℍ with y≥Y, and set m=floor(x/N)∈ℤ. Define τ′=g^(−m)τ. Repeated translation, or the integer-power translation formula, gives Re τ′=x−mN and Im τ′=y.
4. The defining inequalities m≤x/N<m+1, multiplied by the positive real number N, yield 0≤x−mN<N. Thus τ′ satisfies 0≤Re τ′≤N and Im τ′≥Y. The assumed strip bound gives |q(τ′)|≤M.
5. Integer-power invariance from step 2 gives q(τ′)=q(τ), so |q(τ)|≤M. This holds for every τ whose imaginary part is at least Y, with no restriction on its real part. The criterion UpperHalfPlane.isBoundedAtImInfty_iff, using the same witnesses M and Y, now proves the required conclusion.

## Key steps

1. Extend invariance under T^N to all its integer powers.
2. Reduce an arbitrary real part into [0,N) using floor(x/N).
3. Preserve imaginary height and apply the strip bound.
4. Apply the exact uniform eventual-bound criterion.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|isBoundedAtImInfty_iff|binaryFormRepSL|eichlerShimuraMap_injective`
- `theorem.*(T_pow|T_zpow)|def T|lemma.*(T_pow|T_zpow)|coe_T|T_smul`
- `integrable.*exp|exp.*integrable`
- `eq_C_of.*comp|comp.*eq_C|periodic|Periodic`
- `norm_eval|eval.*norm|norm.*eval`
- `rg -n --hidden -g 'dag.json' -g 'decomposition-v*.json' -g '*.lean' 'p02_es_177ebb5a_tb_(strip_coefficient_limit|fixed_form|eval_bound|periodic_strip_bound)' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_tb_decomposition_types.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/Polynomial`
- `/tmp/p02_tb_decomposition_types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected project definitions match the local elaboration environment; local mathlib has the pinned revision and clean Git status. IsEichlerIntegral is coefficientwise differentiation, and binaryFormRepSL uses column substitution, so T^N substitutes (X,Y) ↦ (X,NX+Y). Mathlib supplies homogeneous support and evaluation formulas, exponential decay and integrability, translation action formulas, and the exact eventual-bound criterion. The polynomial searches found no relevant translation-fixed classification; the evaluation searches found no matching homogeneous coefficient-bound estimate. All four proposed types elaborate after import Submission. The proposed names have no match in the current DAG or recorded decompositions. Transitive axiom checks for binaryFormRepSL_apply_coe, modular_T_zpow_smul, isBoundedAtImInfty_iff, and tendsto_pow_mul_exp_neg_atTop_nhds_zero report only propext, Classical.choice, and Quot.sound. These checks validate interfaces and library evidence, not acceptance of the proposed child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/172

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
