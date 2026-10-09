<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.central_telescoping-a1 -->

## Theorem `Submission.p04_pb_60221840b0_central_telescoping`

Let k be a commutative ring, X any type, u,v : X → X, m ≥ 0, and c : Fin(m+1) → X; the universes of k and X may differ. Define Q_j = Fin.insertNth j.castSucc (u(c j)) (fun i : Fin(m+1) => if i < j then u(c i) else v(c i)) and [d]=MonoidAlgebra.single d (1 : k). Then Σ_{j∈Fin(m+1)} ([Q_j ∘ j.castSucc.succAbove] − [Q_j ∘ j.succ.succAbove]) = [v ∘ c] − [u ∘ c] in MonoidAlgebra k (Fin(m+1) → X). No group structure or equivariance is assumed.

Node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.central_telescoping-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/155

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p04_pb_60221840b0_central_telescoping`

```lean
∀ {k X : Type _} [CommRing k] (u v : X → X) (m : ℕ) (c : Fin (m + 1) → X), let Q : Fin (m + 1) → (Fin (m + 2) → X) := fun j => Fin.insertNth j.castSucc (u (c j)) (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i)); (∑ j : Fin (m + 1), (MonoidAlgebra.single (Q j ∘ j.castSucc.succAbove) (1 : k) - MonoidAlgebra.single (Q j ∘ j.succ.succAbove) (1 : k))) = MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k)
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
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.central_telescoping-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data and write x_i=c(i). For every natural number ℓ with 0≤ℓ≤m+1, define T_ℓ : Fin(m+1) → X by T_ℓ(i)=u(x_i) when i.val<ℓ and T_ℓ(i)=v(x_i) otherwise. By the insertion definition, Q_j has entry u(x_r) at positions r≤j and v(x_{r−1}) at positions r>j, interpreting indices by their natural-number values.
2. Deleting position j from Q_j gives T_j. Indeed, at output positions i<j the retained position is i and its entry is u(x_i); at positions i≥j the retained position is i+1 and its entry is v(x_i). The deletion map here is j.castSucc.succAbove, so Q_j ∘ j.castSucc.succAbove=T_j as functions.
3. Deleting position j+1 from Q_j gives T_{j+1}. At output positions i≤j the retained position is i and its entry is u(x_i); at positions i>j the retained position is i+1 and its entry is v(x_i). This deletion map is j.succ.succAbove, giving Q_j ∘ j.succ.succAbove=T_{j+1}.
4. Substitute steps 2 and 3 into the stated sum. It becomes Σ_{j=0}^m ([T_j]−[T_{j+1}]). For each 1≤ℓ≤m, the term [T_ℓ] occurs positively at j=ℓ and negatively at j=ℓ−1. Associativity and commutativity of addition cancel all these interior terms, leaving [T_0]−[T_{m+1}]. When m=0 there are no interior terms, and the same equality holds directly.
5. Every i : Fin(m+1) satisfies 0≤i.val<m+1. Therefore T_0(i)=v(c(i)) and T_{m+1}(i)=u(c(i)) for all i. Thus T_0=v ∘ c and T_{m+1}=u ∘ c. Substituting these endpoint identities proves the required equality.

## Key steps

1. Define mixed tuples T_ℓ with a single transition at ℓ.
2. Identify deletion of position j with T_j.
3. Identify deletion of position j+1 with T_{j+1}.
4. Cancel the interior terms of the telescoping sum.
5. Identify the two endpoint tuples with v ∘ c and u ∘ c.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/401

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
