<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.tate_neg_one_transfer-a1 -->

## Theorem `Submission.p04_tia_tate_neg_one_transfer`

Let k be a commutative ring, G a group with a finite-type structure, A a k-linear G-representation, and H a subgroup equipped with a finite-type structure. For L = G or H, let ν_L : A_L → A^L be the map from coinvariants to invariants induced by the norm Σ_{l∈L} l. Define Tate degree −1 as ker(ν_L), as in Rep.tateHneg1. There exist k-linear maps T : ker(ν_G) → ker(ν_H) and P : ker(ν_H) → ker(ν_G) such that P(T(x)) = [G:H] • x for every x. No normality or finiteness assumption on A is required.

Node: `root.tate_index_annihilation-a1.tate_neg_one_transfer-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/21

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p04_tia_tate_neg_one_transfer`

```lean
∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H], ∃ T : A.tateHneg1 →ₗ[k] (Rep.res H.subtype A).tateHneg1, ∃ P : (Rep.res H.subtype A).tateHneg1 →ₗ[k] A.tateHneg1, ∀ x : A.tateHneg1, P (T x) = H.index • x
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
- Child DAG node: `root.tate_index_annihilation-a1.tate_neg_one_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the hypotheses and put d = [G:H]. Choose a right transversal S and a left transversal U. Multiplication gives bijections H × S → G and U × H → G: each element lies in a represented coset, and cancellation proves uniqueness after identifying its representative. The left-coset set has cardinality d, and inversion identifies left and right cosets, so |S| = |U| = d.
2. For L = G or H, write A_L = A/I_L, where I_L is the k-span of la−a. Define N_L(a) = Σ_{l∈L} la. Left multiplication permutes L, proving N_L(a) ∈ A^L. Right multiplication permutes L, proving N_L(la−a) = 0. Consequently the norm kills I_L and induces ν_L : A_L → A^L with underlying value N_L(a) on [a]_L. This agrees with normBar, and its kernel is the frozen tateHneg1. Every element of A_L has a representative in A.
3. Define π : A_H → A_G by π([a]_H) = [a]_G. This is a well-defined k-linear map because every generator ha−a of I_H belongs to I_G. Define a k-linear map f : A → A_H by f(a) = Σ_{s∈S}[sa]_H. A term is unchanged when s is replaced by hs, because [hsa]_H = [sa]_H. For g ∈ G, right multiplication takes S to the right transversal Sg. Permutation of right cosets and independence of representatives therefore give f(ga) = Σ_s[sga]_H = Σ_s[sa]_H = f(a). Thus f kills every ga−a and its k-span I_G, and descends to a k-linear map τ : A_G → A_H with τ([a]_G) = Σ_s[sa]_H.
4. For a ∈ A, πτ([a]_G) = Σ_s[sa]_G = Σ_s[a]_G = d • [a]_G. Since every class has a representative, πτ = d • id on A_G.
5. The map τ preserves the appropriate norm kernels. Indeed, on a representative a, the underlying element of ν_H(τ([a]_G)) is Σ_sΣ_h hsa = N_G(a), by H × S → G. If x = [a]_G lies in ker(ν_G), then N_G(a) = 0, so ν_H(τ(x)) has zero underlying element. The inclusion A^H → A is injective, hence ν_H(τ(x)) = 0. Restricting τ to these kernels therefore defines a k-linear map T : ker(ν_G) → ker(ν_H).
6. The map π also preserves the appropriate kernels. If y = [a]_H lies in ker(ν_H), then N_H(a) = 0. The bijection U × H → G gives N_G(a) = Σ_{t∈U} tN_H(a) = 0. This is the underlying element of ν_G(π(y)); injectivity of A^G → A makes that invariant element zero. Thus π restricts to a k-linear map P : ker(ν_H) → ker(ν_G).
7. For x ∈ ker(ν_G), include P(T(x)) into A_G. Its image is πτ(x), which equals d • x by step 4. The inclusion of the kernel is linear, so d • x in the kernel has the same underlying element. Injectivity of this inclusion proves P(T(x)) = d • x in ker(ν_G), as required.

## Key steps

1. Choose both transversals and identify their cardinalities with the index.
2. Express the frozen normBar maps on coinvariant representatives.
3. Construct coinvariant projection and right-coset transfer.
4. Compute projection after transfer as the index action.
5. Use the right-coset norm identity to restrict transfer to kernels.
6. Use the left-coset norm identity to restrict projection to kernels.
7. Restrict the composite identity using injectivity of the kernel inclusion.

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

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/440

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
