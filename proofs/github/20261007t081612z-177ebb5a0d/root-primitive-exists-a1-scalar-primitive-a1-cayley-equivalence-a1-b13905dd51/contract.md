<!-- theorem-id: fermat-p02/root.primitive_exists-a1.scalar_primitive-a1.cayley_equivalence-a1 -->

## Theorem `Submission.p02_es_177ebb5a_sp_cayley_equivalence`

Define φ(w)=i(1+w)/(1−w) and ψ(z)=(z−i)/(z+i) for all complex arguments using total complex division. Let D={w∈ℂ : |w|<1} and H={z∈ℂ : Im z>0}. Then φ maps D into H, ψ maps H into D, φ(ψ(z))=z for every z∈H, and ψ(φ(w))=w for every w∈D.

Node: `root.primitive_exists-a1.scalar_primitive-a1.cayley_equivalence-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/37

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_sp_cayley_equivalence`

```lean
(∀ w : ℂ, ‖w‖ < 1 → 0 < (Complex.I * (1 + w) / (1 - w)).im) ∧ (∀ z : ℂ, 0 < z.im → ‖(z - Complex.I) / (z + Complex.I)‖ < 1) ∧ (∀ z : ℂ, 0 < z.im → Complex.I * (1 + (z - Complex.I) / (z + Complex.I)) / (1 - (z - Complex.I) / (z + Complex.I)) = z) ∧ (∀ w : ℂ, ‖w‖ < 1 → (Complex.I * (1 + w) / (1 - w) - Complex.I) / (Complex.I * (1 + w) / (1 - w) + Complex.I) = w)
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

- Parent DAG node: `root.primitive_exists-a1.scalar_primitive-a1`
- Child DAG node: `root.primitive_exists-a1.scalar_primitive-a1.cayley_equivalence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define φ(w)=i(1+w)/(1−w) and ψ(z)=(z−i)/(z+i) on all of ℂ using total complex division. Fix w with |w|<1. Then 1−w≠0, since otherwise w=1, contradicting |w|<1.
2. Write w=x+iy, and put q=(1−x)²+y²=|1−w|²>0. Multiplying numerator and denominator of φ(w) by (1−x)+iy gives φ(w)=[−2y+i(1−x²−y²)]/q. Since x²+y²=|w|²<1, its imaginary part (1−x²−y²)/q is positive. This proves φ(D)⊆H.
3. Fix z=x+iy with y>0. Its denominator s=z+i is nonzero because Im s=y+1>0. Put p=x²+(y+1)²>0 and r=x²+(y−1)². Then p−r=4y>0. Multiplicativity of the complex norm gives |ψ(z)|²=r/p<1. Since |ψ(z)|≥0, this implies |ψ(z)|<1, proving ψ(H)⊆D.
4. For this z, computation over the nonzero denominator s gives 1+ψ(z)=2z/s and 1−ψ(z)=2i/s. The latter is nonzero because 2i and s are nonzero. Consequently φ(ψ(z))=i(2z/s)/(2i/s)=z by field cancellation.
5. For w with |w|<1, put t=1−w≠0. Subtraction and addition over this denominator give φ(w)−i=2iw/t and φ(w)+i=2i/t≠0. Hence ψ(φ(w))=(2iw/t)/(2i/t)=w. Together, these prove all four conclusions.

## Key steps

1. Show 1−w is nonzero on the unit disk.
2. Expand the imaginary part of φ(w) and prove it positive.
3. Compare squared norms of z−i and z+i to show ψ(z) lies in the disk.
4. Compute 1±ψ(z) and cancel nonzero factors to obtain φ(ψ(z))=z.
5. Compute φ(w)±i and cancel nonzero factors to obtain ψ(φ(w))=w.

## Reference use

### local-project

Queries:
- `rg -n 'isExactOn_ball|cayley|Cayley|isExactOn_upperHalfPlane' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b`
- `grep -R -n -E 'isExactOn_ball|def IsExactOn|cayley|Cayley|isExactOn_upperHalfPlane|upperHalfPlane.*[Pp]rimitive' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex --include='*.lean'`
- `HasDerivAt.div|DifferentiableAt.div`
- `HasDerivAt.comp`
- `HasDerivAt.const_mul`
- `def IsEichlerIntegral|def eichlerShimuraMap|def IsEquivariantPrimitiveWith`
- `p02_es_177ebb5a_sp_cayley_equivalence`
- `p02_es_177ebb5a_sp_cayley_derivatives`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_sp_cayley_interfaces.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-scalar-primitive-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/Submission.lean`
- `/tmp/p02_sp_cayley_interfaces.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The requested rg search could not run because rg is unavailable; grep and Python supplied the local searches. HasPrimitives.lean defines Complex.IsExactOn using ordinary HasDerivAt and provides DifferentiableOn.isExactOn_ball. The searched complex-analysis directory contained no Cayley-transform or upper-half-plane primitive result matching the queries. The derivative files provide the required quotient and chain rules. The project definition confirms the coefficientwise ordinary-derivative context. Neither proposed identifier occurred in Submission, the snapshot, or the current DAG/node metadata. Both exact proposed types elaborated after import Submission under Lean 4.33.1. All installed dependency revisions matched the manifest with clean tracked sources; the four consulted mathlib files and three directly imported project definition files matched the snapshot. Transitive axiom checks for the disk-primitive theorem, IsExactOn, quotient rule, chain rule, constant multiplication rule, and differentiability quotient rule returned only propext, Classical.choice, and Quot.sound. These checks validate interfaces and library infrastructure, not comparator acceptance of new proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/157

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
