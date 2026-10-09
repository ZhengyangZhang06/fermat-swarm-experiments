<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.equivariant_prism_components-a1 -->

## Theorem `Submission.p04_prism_a8325b9888_equivariant_components`

Let k be a commutative ring and G a group in the same universe, H ≤ G, and u,v : G → G satisfy u(hg)=h u(g) and v(hg)=h v(g) for all h ∈ H and g ∈ G. Let C be Rep.standardComplex k G restricted to H. For n ≥ 0 and c=(g₀,…,gₙ), define Pₙ(c)=Σⱼ₌₀ⁿ (−1)ʲ[ug₀,…,ugⱼ,vgⱼ,…,vgₙ] in the free k-module on (n+2)-tuples, where [t]=MonoidAlgebra.single t 1. Precisely, the j-th tuple is Fin.insertNth j.castSucc (u(c j)) (fun i => if i < j then u(c i) else v(c i)). There exists a family of morphisms Dₙ : Cₙ → Cₙ₊₁ in Rep k H such that Dₙ([c])=Pₙ(c) for every n and c. No finiteness or normality assumption is imposed.

Node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.equivariant_prism_components-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/149

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p04_prism_a8325b9888_equivariant_components`

```lean
∀ {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) (u v : G → G), (∀ (h : H) (g : G), u ((h : G) * g) = (h : G) * u g) → (∀ (h : H) (g : G), v ((h : G) * g) = (h : G) * v g) → let P : ∀ n : ℕ, (Fin (n + 1) → G) → MonoidAlgebra k (Fin (n + 2) → G) := fun n c => ∑ j : Fin (n + 1), MonoidAlgebra.single (Fin.insertNth j.castSucc (u (c j)) (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i))) ((-1 : k) ^ j.val); let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.standardComplex k G); ∃ D : ∀ n : ℕ, C.X n ⟶ C.X (n + 1), ∀ (n : ℕ) (c : Fin (n + 1) → G), (D n).hom (MonoidAlgebra.single c (1 : k)) = P n c
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

- Parent DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1`
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.equivariant_prism_components-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, G, H, u, v and the two equivariance hypotheses. The underlying module of Cₙ is MonoidAlgebra k (Fin(n+1) → G), the free k-module on these tuples. Write e_c=single c 1. Restriction changes only the acting group, and its action satisfies h·e_c=e_{hc}, where (hc)(i)=(h:G)c(i).
2. For j ∈ Fin(n+1), let Qₙ,ⱼ(c)=Fin.insertNth j.castSucc (u(c j)) (fun i => if i<j then u(c i) else v(c i)). Before position j this tuple has entries u(c i); position j is the inserted u(c j); after position j its entry at position a is v(c(a−1)). Hence Qₙ,ⱼ(c) is exactly (ug₀,…,ugⱼ,vgⱼ,…,vgₙ). Define Pₙ(c)=Σⱼ single Qₙ,ⱼ(c) ((−1:k)ʲ). Since a·single t 1=single t a, this is the prism sum in the statement.
3. The universal property of the free k-module gives a k-linear map Dₙ with Dₙ(e_c)=Pₙ(c). Explicitly, if x=Σ_c a_c e_c is its finite coefficient expansion, set Dₙ(x)=Σ_c a_c Pₙ(c). The uniquely determined coefficients make this well-defined; coefficientwise addition and scalar multiplication show it is k-linear, including when k is the zero ring.
4. For h ∈ H, Qₙ,ⱼ(hc)=hQₙ,ⱼ(c). Indeed, before and at the inserted position this follows from u((h:G)g)=(h:G)u(g); after that position it follows from the corresponding identity for v. The comparison i<j depends only on indices and is unchanged by h.
5. The action on the target free module sends single t a to single (ht) a and is k-linear. Applying step 4 termwise therefore gives Pₙ(hc)=h·Pₙ(c). On each generator, Dₙ(h·e_c)=Dₙ(e_{hc})=Pₙ(hc)=h·Dₙ(e_c). Both sides are k-linear functions of the input, so this identity holds on every finite coefficient expansion and thus on every element of Cₙ.
6. Consequently Dₙ is H-equivariant and defines a morphism Cₙ → Cₙ₊₁ in Rep k H. Carrying out this construction for each natural number n gives the required family, with its generator formula supplied by step 3.

## Key steps

1. Identify the restricted complex objects as free modules with diagonal H-action.
2. Express each prism tuple using Fin.insertNth and form its signed sum.
3. Extend the generator assignment k-linearly.
4. Use equivariance of u and v to prove equivariance of every prism tuple.
5. Extend equivariance from generators to all elements and obtain the family of Rep morphisms.

## Reference use

### local-project

Queries:
- `standardComplex|prism|Homotopy`
- `prism|homotopy.*equivariant|equivariant.*homotopy`
- `def insertNth|theorem insertNth|predAbove`
- `def res|abbrev res|def ofMulAction|ofMulAction.*single|def of|structure Hom|def lift`
- `lhom_ext|lift.*single`
- `linearizeMap_single|def linearize|ofMulAction.*single|def ofMulAction`
- `p04_prism_a8325b9888_(equivariant_components|boundary_identity)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/Resolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/MonoidAlgebra/Module.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/Homology/Homotopy.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/tmp/p04-prism-a8325b9888-contracts/ContractTypes.lean`
- `/tmp/p04-prism-a8325b9888-contracts/ContractTypes.log`

The manifest pins project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Resolution.lean supplies the free tuple modules and alternating differential through d_of and d_apply; restriction preserves underlying linear maps; ofMulAction_single describes the diagonal action. Fin.insertNth expresses the prism tuple without index-bound proof terms. Homotopy supplies the required degree-zero and successor component identities. No existing prism theorem was found in the searched project Definitions and mathlib RepresentationTheory directories. Both proposed names are absent from the active DAG. Both exact propositions elaborated after import Submission using the existing cached Submission module, and the coefficient scalar action was checked by proving a • single x 1 = single x a. Checked library declarations depend only on propext, Classical.choice, and Quot.sound; local dependency revisions match their pins and have no tracked modifications. Validation limitation: rebuilding the unchanged frozen Submission itself fails on its existing attribute reference to the missing constant Representation.TateResCor.cosetDecomp_apply. The frozen source was not changed, and these checks do not constitute comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/328

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
