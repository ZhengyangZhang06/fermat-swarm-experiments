<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.tate_zero_transfer-a1.invariant_restriction_norm_range-a1 -->

## Theorem `Submission.p04_tz91_invariant_restriction_norm_range`

Let k be a commutative ring, G a group with Fintype G, A a k-linear G-representation, and H a subgroup with Fintype H. Put B = Rep.res H.subtype A. For L = G or H, let ν_L be normBar, the map from coinvariants to invariants induced by N_L(v) = Σ_{l∈L} l v. There exists a k-linear map j : A^G → A^H whose underlying vector equals its input and such that j(im ν_G) ⊆ im ν_H. No normality of H or finiteness of A is assumed.

Node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1.invariant_restriction_norm_range-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/91

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p04_tz91_invariant_restriction_norm_range`

```lean
∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H], ∃ j : A.ρ.invariants →ₗ[k] (Rep.res H.subtype A).ρ.invariants, (∀ a : A.ρ.invariants, (j a : A) = (a : A)) ∧ LinearMap.range A.ρ.normBar ≤ (LinearMap.range (Rep.res H.subtype A).ρ.normBar).comap j
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

- Parent DAG node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1`
- Child DAG node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1.invariant_restriction_norm_range-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write B for A restricted to H, and N_L(v) = Σ(l ∈ L) l v for L = G or H. Left multiplication permutes L, so N_L(v) is L-invariant. Right multiplication permutes L, so N_L(l v − v) = 0. Hence N_L kills the span of these differences and induces ν_L on coinvariants. By the frozen definition, ν_L is normBar and ν_L([v]) is normToInvariants(v). Every coinvariant has a representative, so the image of ν_L consists exactly of these norm values.
2. Define j on G-invariants by retaining the underlying vector. Every element of H acts through an element of G, so that vector is H-invariant. Addition and scalar multiplication are inherited from A, making j k-linear, and its underlying vector is unchanged.
3. Choose a set S with exactly one representative of each right coset Hs. This is a finite set since G is finite. The map H × S → G sending (h,s) to hs is surjective by the definition of representatives. If hs = h′ s′, their right cosets agree, hence s = s′, and cancellation then gives h = h′. Thus this map is bijective. For v ∈ A put w = Σ(s ∈ S) s v. Linearity and this bijection give N_H(w) = Σ(h ∈ H)Σ(s ∈ S) hs v = N_G(v). These equalities hold as H-invariant elements after applying j to the ambient norm.
4. Let y belong to the range of ν_G. By step 1 choose v with y = ν_G([v]). Step 3 gives j(y) = ν_H([w]), so j(y) lies in the range of ν_H. This is precisely range(ν_G) ≤ comap(j, range(ν_H)), proving both required properties of j.

## Key steps

1. Identify normBar values with norms of coinvariant representatives.
2. Construct the linear inclusion of ambient invariants into subgroup invariants.
3. Use the right-coset multiplication bijection to express every ambient norm as a subgroup norm.
4. Deduce the required inclusion of norm ranges.

## Reference use

### local-project

Queries:
- `tateH0|normBar|cosetNormInvariants|tateH0Res|tateH0Cores`
- `norm|invariants|res|mk_surjective`
- `p04_tz91_|TateResCor|tateH0Res|tateH0Cores`
- `lean_name|depth|candidate_commit|proof_base_commit`
- `def mapQ|theorem mapQ_apply|lemma mapQ_apply|mapQ_mkQ|mapQ_comp|mkQ_apply|mkQ_surjective`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions/Def_GroupCohomology_TateCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Coinvariants.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Coset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Index.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`
- `/tmp/p04-tz91-dependency-audit.json`
- `/tmp/p04-tz91-decomposition-6yojlzlg/contracts.json`
- `/tmp/p04-tz91-decomposition-6yojlzlg/TypeAudit.lean`
- `/tmp/p04-tz91-decomposition-6yojlzlg/TypeAudit.log`
- `/tmp/p04-tz91-decomposition-6yojlzlg/AssemblyAudit.lean`
- `/tmp/p04-tz91-decomposition-6yojlzlg/AssemblyAudit.log`
- `/tmp/p04-tz91-decomposition-6yojlzlg/Submission.log`

The snapshot confirms the normBar quotient definition, surjectivity of the coinvariant projection, the unchanged underlying module under restriction, coset decomposition, and Submodule.mapQ. No degree-zero subgroup transfer implementation or proposed-name collision was found in the searched definitions and DAG. Snapshot revisions match the manifest; all nine installed dependencies match their pinned revisions and have clean source trees. Both proposed types elaborate against unchanged frozen definitions with Lean 4.33.1. Instance checks confirm inherited repeated addition, and a warning-free conditional assembly proves the parent from the two contracts. Audited infrastructure has only propext, Classical.choice, and Quot.sound as transitive axioms. However, the required import Submission gate remains blocked: unchanged Submission.lean fails at line 10 on the unknown constant Representation.TateResCor.cosetDecomp_apply. These checks do not establish comparator acceptance or authorize child activation.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/262

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
