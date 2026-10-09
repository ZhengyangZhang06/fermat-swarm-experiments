<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.tate_zero_transfer-a1 -->

## Theorem `Submission.p04_tia_tate_zero_transfer`

Let k be a commutative ring, G a group with a finite-type structure, A a k-linear G-representation, and H a subgroup equipped with a finite-type structure. For L = G or H, write A^L for the invariant submodule, A_L for the coinvariants, and ν_L : A_L → A^L for the map induced by the norm Σ_{l∈L} l. Define Tate degree zero as A^L/im(ν_L), as in Rep.tateH0. There exist k-linear maps R from the G quotient to the H quotient and C back such that C(R(x)) = [G:H] • x for every x. No normality or finiteness assumption on A is required.

Node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/21

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/134, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/135

## Lean problem

Declaration: `Submission.p04_tia_tate_zero_transfer`

```lean
∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H], ∃ R : A.tateH0 →ₗ[k] (Rep.res H.subtype A).tateH0, ∃ C : (Rep.res H.subtype A).tateH0 →ₗ[k] A.tateH0, ∀ x : A.tateH0, C (R x) = H.index • x
```

### Frozen project context

`Fermat/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean` at `2475a3790d7ba0c3b10be8086001b154a45be597` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
attribute [-simp] Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_index_annihilation-a1`
- Child DAG node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the hypotheses and write d = [G:H]. Choose left-coset representatives T and right-coset representatives S. Multiplication gives bijections T × H → G and H × S → G: each element belongs to one represented coset, and equality of expressions identifies first the representative and then the H factor by cancellation. Thus |T| = d, and inversion of cosets also gives |S| = d.
2. For L = G or H, let I_L be the k-span of la−a, and write A_L = A/I_L. Set N_L(a) = Σ_{l∈L} la. Left multiplication permutes L, so N_L(a) is invariant. Right multiplication permutes L, so N_L(la−a) = 0; linearity shows that N_L kills I_L. It therefore induces ν_L : A_L → A^L, with ν_L([a]_L) = N_L(a), regarded as an invariant element. Every coinvariant class has a representative, so im(ν_L) consists exactly of these norm values. This is the normBar and quotient used in the frozen definition of tateH0.
3. Inclusion j : A^G → A^H is k-linear. The right-coset decomposition gives N_G(b) = Σ_{s∈S}Σ_{h∈H} hsb = N_H(Σ_{s∈S} sb). Therefore j sends each element of im(ν_G) into im(ν_H), using the representative description in step 2. It descends to a k-linear quotient map R : A^G/im(ν_G) → A^H/im(ν_H).
4. For a ∈ A^H define c(a) = Σ_{t∈T} ta. Replacing t by th does not change its term because ha = a. Thus the sum is independent of representatives. For g ∈ G, left multiplication gives another left transversal gT; evaluating the same representative-independent sum on gT proves g c(a) = c(a). Hence c maps into A^G. The formula is k-linear because the action and finite summation are k-linear.
5. For b ∈ A, use the bijection T × H → G to obtain c(N_H(b)) = Σ_tΣ_h thb = N_G(b). Thus c sends im(ν_H) into im(ν_G), again using step 2, and descends to a k-linear quotient map C : A^H/im(ν_H) → A^G/im(ν_G).
6. Every element x of A.tateH0 has a representative a ∈ A^G. Each t ∈ T fixes a, so c(j(a)) = Σ_t a = d • a. Passing to the quotient, whose projection is additive, gives C(R(x)) = d • x. This proves the required factorization.

## Key steps

1. Choose left and right transversals and their multiplication bijections.
2. Identify the normBar image with norm values of representatives.
3. Descend invariant inclusion using the right-coset norm identity.
4. Construct the invariant coset sum and descend it using the left-coset norm identity.
5. Compute the composite on invariant representatives.

## Reference use

### local-project

Queries:
- `tateCohomology|tateH0|tateHneg1|index|res.*cor|cores.*res`
- `transfer|corestriction|cores|index.*smul|smul.*index|restriction|res_comp`
- `TateResCor|tateH0Cores|tateHneg1Cores`
- `isZero_iff_subsingleton|theorem index|def index|span|quotient`
- `p04_tia_(cohomology_transfer|homology_transfer|tate_zero_transfer|tate_neg_one_transfer)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions/Def_GroupCohomology_TateCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupHomology/Functoriality.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/Resolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Coinvariants.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Index.lean`
- `/tmp/p04-tia-decomposition-5j4m4no2/contracts.json`
- `/tmp/p04-tia-decomposition-5j4m4no2/TypeAudit.lean`
- `/tmp/p04-tia-decomposition-5j4m4no2/TypeAudit.log`
- `/tmp/p04-tia-decomposition-5j4m4no2/InstanceAudit.log`
- `/tmp/p04-tia-decomposition-5j4m4no2/AssemblyAudit.lean`
- `/tmp/p04-tia-decomposition-5j4m4no2/AssemblyAudit.log`
- `/tmp/p04-tia-decomposition-5j4m4no2/DependencyAudit.json`
- `/tmp/p04-tia-decomposition-5j4m4no2/SubmissionImportAudit.log`

Verified clean snapshot revisions: project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. All nine installed dependencies match the pinned manifest and have clean source trees. The sources confirm the four Tate branches, norm kernel and quotient, homogeneous resolution, and both differential conventions, including inverse action in homology. Existing homology corestriction infrastructure was found, but no general transfer-composition theorem matching these obligations. No proposed identifier occurs in the inspected DAG or project declarations. All four exact propositions elaborate against the unchanged frozen definitions; a warning-free conditional Lean proof verifies that their specializations imply the exact parent contract. Instance inspection confirms repeated-addition actions, including the inherited kernel action. Audited definitions and comparison infrastructure use only propext, Classical.choice, and Quot.sound. The required direct Submission import gate remains blocked: the inherited Submission.lean reports unknown constant Representation.TateResCor.cosetDecomp_apply at line 10. No source was changed to conceal that failure, and these checks do not constitute comparator acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/363

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
