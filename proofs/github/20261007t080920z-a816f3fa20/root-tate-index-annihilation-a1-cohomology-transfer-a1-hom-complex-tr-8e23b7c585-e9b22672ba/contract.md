<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1.coset_summand_independence-a1 -->

## Theorem `Submission.p04_hca_bc7c754a4b_summand_eq_of_coset_eq`

Let k be a commutative ring, G a group, A and B k-linear G-representations in the same representation universe, and H ≤ G. Let F : Res_H B → Res_H A be an H-equivariant k-linear map. If s,t ∈ G have the same left coset in G/H, then for every x ∈ B, ρ_A(s)(F(ρ_B(s⁻¹)x)) = ρ_A(t)(F(ρ_B(t⁻¹)x)). No finiteness or normality assumption is required.

Node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1.coset_summand_independence-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/150

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p04_hca_bc7c754a4b_summand_eq_of_coset_eq`

```lean
∀ {k G : Type _} [CommRing k] [Group G] (A B : Rep k G) (H : Subgroup G) (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (s t : G), (QuotientGroup.mk s : G ⧸ H) = QuotientGroup.mk t → ∀ x : B, A.ρ s (F.hom (B.ρ s⁻¹ x)) = A.ρ t (F.hom (B.ρ t⁻¹ x))
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

- Parent DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1`
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1.coset_summand_independence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k,G,A,B,H,F,s,t and the assumed equality of left cosets. Fix x ∈ B. Equality of these cosets means s⁻¹t ∈ H. Define h ∈ H to have underlying group element s⁻¹t. Then t = sh, where subgroup elements are viewed in G.
2. Put y = ρ_B(s⁻¹)x. Since t = sh, inversion gives t⁻¹ = h⁻¹s⁻¹. The representation multiplication laws therefore give ρ_A(t)F(ρ_B(t⁻¹)x) = ρ_A(s)ρ_A(h)F(ρ_B(h⁻¹)y).
3. The inverse h⁻¹ belongs to H. H-equivariance of F gives F(ρ_B(h⁻¹)y) = ρ_A(h⁻¹)F(y). Substituting this equality into step 2 gives ρ_A(t)F(ρ_B(t⁻¹)x) = ρ_A(s)ρ_A(h)ρ_A(h⁻¹)F(y).
4. The representation laws imply ρ_A(h)ρ_A(h⁻¹) = ρ_A(1) = id. Thus the expression in step 3 equals ρ_A(s)F(y) = ρ_A(s)F(ρ_B(s⁻¹)x). Reversing this equality proves the stated identity. Since x was arbitrary, it holds for every x ∈ B.

## Key steps

1. Extract h = s⁻¹t ∈ H from equality of left cosets, obtaining t = sh.
2. Expand the conjugated summand using the representation multiplication laws.
3. Move ρ_B(h⁻¹) through F by H-equivariance.
4. Cancel ρ_A(h)ρ_A(h⁻¹) and reverse the resulting equality.

## Reference use

### local-project

Queries:
- `coset.*[Aa]verag|[Aa]verag.*coset|[Hh]om.*[Tt]ransfer|[Tt]ransfer.*[Hh]om`
- `def res|res_ρ|res_hom|resFunctor`
- `def res|def ρ|abbrev ρ|structure Hom|def mkHom|comm_apply|hom_apply|def hom`
- `smul_mk|smul_out|mul_left|smul.*out|MulAction`
- `theorem sum_comp|lemma sum_comp|sum_equiv|sum_bijective`
- `p04_hca_bc7c754a4b_summand_eq_of_coset_eq|p04_hca_bc7c754a4b_sum_equivariant`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain --untracked-files=no`
- `command -v lean lake elan python3`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Coset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/Submission.lean`

The manifest pins project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib has that HEAD and no tracked modifications; inspected Rep/Basic, Rep/Res, and Coset/Defs and Basic files match the snapshot byte for byte. Rep.hom_comm_apply supplies equivariance, and restriction preserves underlying vector spaces. QuotientGroup.eq characterizes equality of left cosets by s⁻¹t ∈ H; the quotient-action API supplies left multiplication and representative identities without normality. Finite-sum reindexing is available. The targeted averaging search found no relevant match, and neither proposed identifier occurs in the inspected DAG, node contracts, or Submission source. No Lean executable or compiled Submission was available, so elaboration and transitive axiom checks were not performed; these source checks do not constitute comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/226

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
