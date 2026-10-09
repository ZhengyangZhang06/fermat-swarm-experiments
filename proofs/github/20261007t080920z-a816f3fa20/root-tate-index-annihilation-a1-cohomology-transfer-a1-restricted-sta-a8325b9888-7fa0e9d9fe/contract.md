<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1 -->

## Theorem `Submission.p04_rsh_82a013d1d0_prism_homotopy`

Let k be a commutative ring and G a group in the same universe, and let H ≤ G. Set C = Res_H(Rep.standardComplex k G). Let u,v : G → G satisfy u(hg) = h u(g) and v(hg) = h v(g) for every h ∈ H and g ∈ G. Suppose U,V : C → C are chain maps in Rep k H such that, for every n ≥ 0 and tuple c : Fin(n+1) → G, U_n sends the free generator [c] to [u ∘ c] and V_n sends [c] to [v ∘ c]. Then there exists a chain homotopy from V to U, with convention V − U = ∂D + D∂. No finiteness or normality assumption is required.

Node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/138

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/154, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/155

## Lean problem

Declaration: `Submission.p04_rsh_82a013d1d0_prism_homotopy`

```lean
∀ {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) (u v : G → G), (∀ (h : H) (g : G), u ((h : G) * g) = (h : G) * u g) → (∀ (h : H) (g : G), v ((h : G) * g) = (h : G) * v g) → let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.standardComplex k G); ∀ U V : CategoryTheory.End C, (∀ (n : ℕ) (c : Fin (n + 1) → G), (U.f n).hom (MonoidAlgebra.single c (1 : k)) = MonoidAlgebra.single (u ∘ c) (1 : k)) → (∀ (n : ℕ) (c : Fin (n + 1) → G), (V.f n).hom (MonoidAlgebra.single c (1 : k)) = MonoidAlgebra.single (v ∘ c) (1 : k)) → Nonempty (Homotopy V U)
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

- Parent DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1`
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data. Write [g₀,…,gₙ] for the generator MonoidAlgebra.single c 1 of C_n. Restriction preserves the underlying modules and differentials. In positive degree the differential is the alternating sum of vertex deletions, and the outgoing differential in degree zero is zero.
2. For n ≥ 0 define D_n on generators by D_n[g₀,…,gₙ] = Σ_{j=0}^n (−1)^j[ug₀,…,ug_j,vg_j,…,vgₙ], and extend k-linearly. This extension exists because C_n is the free k-module on these tuples. For h ∈ H, equivariance of u and v makes each displayed prism tuple for (hg₀,…,hgₙ) the simultaneous h-translate of the corresponding tuple for (g₀,…,gₙ). The action on the free module is k-linear, so D_n is H-equivariant. It is consequently a morphism C_n → C_{n+1} in Rep k H.
3. Fix n ≥ 1 and a generator c = [g₀,…,gₙ]. Expand ∂_{n+1}D_n(c) and D_{n−1}∂_n(c). In the j-th prism summand, delete a position a < j. Its coefficient is (−1)^{j+a}. The resulting tuple equals the tuple obtained by first deleting original vertex a and then taking prism position j−1: both tuples omit ug_a from the initial u-segment and have duplicated transition vertex g_j. The coefficient of the latter term in D_{n−1}∂_n(c) is (−1)^{a+j−1}. These coefficients are additive inverses, so the terms cancel.
4. In the j-th prism summand, delete a position a > j+1. Its coefficient is (−1)^{j+a}. This produces the same tuple as first deleting original vertex a−1 and then taking prism position j: both omit vg_{a−1} from the final v-segment and retain transition vertex g_j. The coefficient in D_{n−1}∂_n(c) is (−1)^{a−1+j}, so these terms cancel as well.
5. These cancellations account for every term of D_{n−1}∂_n(c) exactly once. Indeed, such a term is indexed by an original deleted position b with 0 ≤ b ≤ n and a subsequent prism position t with 0 ≤ t ≤ n−1. If b ≤ t, it pairs with j = t+1 and a = b from step 3. If b > t, it pairs with j = t and a = b+1 from step 4. These cases are disjoint and exhaustive, and the formulas invert the respective pairings.
6. The remaining terms in ∂_{n+1}D_n(c) delete positions j and j+1 of the j-th prism. Deleting j has coefficient (−1)^{2j} = 1 and yields A_j = [ug₀,…,ug_{j−1},vg_j,…,vgₙ]. Deleting j+1 has coefficient (−1)^{2j+1} = −1 and yields −B_j, where B_j = [ug₀,…,ug_j,vg_{j+1},…,vgₙ]. For 0 ≤ j < n, B_j = A_{j+1}, so their sum telescopes to A₀ − Bₙ = [vg₀,…,vgₙ] − [ug₀,…,ugₙ]. Thus ∂_{n+1}D_n(c) + D_{n−1}∂_n(c) = V_n(c) − U_n(c), using the assumed formulas for U and V.
7. In degree zero, D₀[g] = [ug,vg], and its boundary is [vg] − [ug] = V₀[g] − U₀[g]. There is no contribution from an outgoing degree-zero differential. This proves the required identity in that degree also. Since generators span and every map involved is k-linear, the identities hold on every element in every degree.
8. Define the two-index homotopy component from C_i to C_j to be D_i when j = i+1, using the corresponding equality of degrees, and zero otherwise. The components vanish outside the required chain-homotopy shape. Steps 6 and 7 give V_i = dNext_i(D) + prevD_i(D) + U_i, precisely the commutation condition in Homotopy V U. Together with H-equivariance from step 2, these components define such a homotopy and hence a witness to Nonempty (Homotopy V U).

## Key steps

1. Identify the restricted standard complex with free tuple modules and alternating deletion differentials.
2. Define the signed prism operators and prove their H-equivariance.
3. Cancel deletions before the transition against D∂ terms.
4. Cancel deletions after the transition against D∂ terms.
5. Verify the pairings exhaust D∂ without duplication.
6. Telescope the transition deletions to the all-v tuple minus the all-u tuple.
7. Check degree zero separately and extend the identities by linearity.
8. Package the operators as a chain homotopy from V to U.

## Reference use

### local-project

Queries:
- `standardComplex|HomotopyEquiv|coset.*[Rr]epr|[Rr]epr.*coset`
- `rightTransversal|RightTransversal|right.*[Rr]epresent|exists.*transversal|leftTransversal`
- `def res|resFunctor`
- `restricted.*standard.*[Hh]omotopy|standard.*[Hh]omotopy.*restrict|standardComplex.*resFunctor`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/p04_rsh_82a013d1d0_types/TypesMathlib.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/p04_rsh_82a013d1d0_types/TypesSubmission.lean`
- `#print axioms Rep.standardComplex.d_eq`
- `#print axioms Rep.standardComplex.d_single`
- `#print axioms Representation.linearizeMap_single`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/Resolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Complement.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Action.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/Homology/Homotopy.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean`

The manifest pins project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Resolution.lean identifies degree-n generators and supplies the alternating deletion formulas d_eq and d_single. Complement.lean provides right transversals without finiteness assumptions. Res.lean and Action.lean confirm restriction and equivariant linearization. Homotopy.lean uses the convention f = dD + Dd + g, so the positive prism gives Homotopy V U. ChainHomotopy.lean provides related simplicial-to-chain infrastructure. The targeted restricted-standard-homotopy search returned no matches in the snapshot's RepresentationTheory and project/Definitions trees. All six inspected library files match the clean pinned mathlib checkout. The three queried library lemmas depend only on propext, Classical.choice, and Quot.sound. Both proposed types elaborated with Lean 4.33.1 independently under import Mathlib and under import Submission from the cached local p04 worktree; neither expression uses a candidate theorem. The elaborated component maps are Rep.Hom.hom, retaining H-equivariance. Both proposed identifiers are absent from the inspected DAG and handoff metadata. These checks establish type compatibility, not proof acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/550

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
