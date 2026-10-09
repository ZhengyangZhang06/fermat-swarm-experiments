<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.noncentral_cancellation-a1 -->

## Theorem `Submission.p04_pb_60221840b0_noncentral_cancellation`

Let k be a commutative ring, X any type, and u,v : X → X; their universes may differ. For m ≥ 0, d : Fin(m+1) → X and j : Fin(m+1), define Q_m(d,j) = Fin.insertNth j.castSucc (u(d j)) (fun i => if i < j then u(d i) else v(d i)). Write S(d,r)=MonoidAlgebra.single d r. For every n ≥ 0 and c : Fin(n+2) → X, the following equality holds in MonoidAlgebra k (Fin(n+2) → X): Σ_{j∈Fin(n+2)} Σ_{a∈Fin(n+3), a.val<j.val or j.val+1<a.val} S(Q_{n+1}(c,j) ∘ a.succAbove, (−1)^(j.val+a.val)) + Σ_{b∈Fin(n+2)} Σ_{t∈Fin(n+1)} S(Q_n(c ∘ b.succAbove,t), (−1)^(b.val+t.val)) = 0. No group structure or equivariance is assumed.

Node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.noncentral_cancellation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/155

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p04_pb_60221840b0_noncentral_cancellation`

```lean
∀ {k X : Type _} [CommRing k] (u v : X → X) (n : ℕ) (c : Fin (n + 2) → X), let Q : ∀ m : ℕ, (Fin (m + 1) → X) → Fin (m + 1) → (Fin (m + 2) → X) := fun m d j => Fin.insertNth j.castSucc (u (d j)) (fun i : Fin (m + 1) => if i < j then u (d i) else v (d i)); (∑ j : Fin (n + 2), ∑ a : Fin (n + 3) with a.val < j.val ∨ j.val + 1 < a.val, MonoidAlgebra.single (Q (n + 1) c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) + (∑ b : Fin (n + 2), ∑ t : Fin (n + 1), MonoidAlgebra.single (Q n (c ∘ b.succAbove) t) ((-1 : k) ^ (b.val + t.val))) = 0
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

- Parent DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1`
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.noncentral_cancellation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data, put N=n+1, and write x_i=c(i). Identify finite indices with their natural-number values. By the insertion definition, Q_m(d,j) has entry u(d_r) at positions r≤j and v(d_{r−1}) at positions r>j. Deleting position a replaces the argument r by r when r<a and by r+1 when r≥a.
2. Consider a first-sum index with a<j. Set b=a and t=j−1. Since 1≤j≤N, we have 0≤t≤N−1 and 0≤b≤N. Put d=c ∘ b.succAbove, so d_r=x_r for r<a and d_r=x_{r+1} for r≥a. At output positions s≤t, deleting position a from Q_N(c,j) gives u(x_s) for s<a and u(x_{s+1}) for s≥a; these are u(d_s). At positions s>t, we have s≥j>a, and the deleted tuple has entry v(x_s)=v(d_{s−1}). Thus Q_N(c,j) ∘ a.succAbove = Q_{N−1}(d,t).
3. Consider instead a first-sum index with a>j+1. Set b=a−1 and t=j. The bounds a≤N+1 and a≥j+2 imply 0≤t≤N−1 and 0≤b≤N. Put d=c ∘ b.succAbove. At positions s≤j, the deleted tuple has entry u(x_s)=u(d_s), because s<a−1. At positions j<s<a it has entry v(x_{s−1})=v(d_{s−1}); at positions s≥a it has entry v(x_s)=v(d_{s−1}). These cases exhaust all output positions, proving Q_N(c,j) ∘ a.succAbove = Q_{N−1}(d,t).
4. These assignments give a bijection with all second-sum indices (b,t). Explicitly, if b≤t, take j=t+1 and a=b. Then j≤N, a<j, and the assignment in step 2 returns (b,t). If b>t, take j=t and a=b+1. Then a≤N+1, a>j+1, and step 3 returns (b,t). Conversely, the first case produces b≤t, the second produces b>t, and these inverse formulas recover the original (j,a). The two cases are disjoint and exhaustive.
5. In both cases j+a=b+t+1. Hence (−1)^(j+a)=−(−1)^(b+t) in k. Steps 2 and 3 identify the corresponding tuples. Additivity of MonoidAlgebra.single in its coefficient therefore makes each paired sum equal to S(d,−r)+S(d,r)=S(d,0)=0, where r=(−1)^(b+t).
6. Reindex the filtered first double sum using the bijection of step 4 and combine it with the second double sum. Finite-sum distributivity and step 5 make every summand zero. This proves the asserted equality. The bijection is between indices, so repeated tuples and noninjective u or v do not affect the argument.

## Key steps

1. Evaluate the inserted prism tuple coordinatewise.
2. Identify deletion before the transition with the smaller prism having transition j−1.
3. Identify deletion after the transition with the smaller prism having transition j.
4. Construct the inverse pairing using the exhaustive cases b≤t and b>t.
5. Show paired coefficient exponents differ by one.
6. Reindex the finite sums and cancel every paired term.

## Reference use

### local-project

Queries:
- `namespace standardComplex|standardComplex.d`
- `removeNth_insertNth|insertNth_apply_same|insertNth_apply_succAbove|insertNth_apply_below|insertNth_apply_above`
- `prism|prism_boundary|prismBoundary`
- `cosetDecomp_apply`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions/Def_GroupCohomology_TateCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/Resolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`

The manifest pins project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Resolution.lean defines the differential for arbitrary types and supplies d_of and d_single. Tuple/Basic.lean supplies insertion evaluation and insertNth_comp_succAbove. No prism identity was found in the searched project definitions, representation theory, or algebraic topology directories. All nine installed dependencies match their pins and have clean tracked sources. Both proposed expressions elaborate with Lean 4.33.1 against the unchanged frozen imports; the inspected library lemmas depend only on propext, Classical.choice, and Quot.sound. Neither proposed name is reserved in the current DAG. However, compiling unchanged Submission.lean fails at line 10 on the absent Representation.TateResCor.cosetDecomp_apply. Thus the required import Submission gate remains blocked; these checks do not authorize child activation or establish comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/320

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
