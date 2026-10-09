<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.cohomology_transfer-a1 -->

## Theorem `Submission.p04_tia_cohomology_transfer`

Let k be a commutative ring, G a group with a finite-type structure, A a k-linear G-representation, H a subgroup equipped with a finite-type structure, and n a natural number. Use the common universe required by groupCohomology. There exist k-linear maps R : Hⁿ(G,A) → Hⁿ(H,Res_H A) and C : Hⁿ(H,Res_H A) → Hⁿ(G,A) such that C(R(x)) = [G:H] • x for every x, where • is repeated addition. No normality of H or finiteness of A is assumed.

Node: `root.tate_index_annihilation-a1.cohomology_transfer-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/21

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/138, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/139

## Lean problem

Declaration: `Submission.p04_tia_cohomology_transfer`

```lean
∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ), ∃ R : groupCohomology A n →ₗ[k] groupCohomology (Rep.res H.subtype A) n, ∃ C : groupCohomology (Rep.res H.subtype A) n →ₗ[k] groupCohomology A n, ∀ x : groupCohomology A n, C (R x) = H.index • x
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
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data and put d = [G:H]. Choose a left transversal T, with one representative of each coset tH, and a right transversal S, with one representative of each coset Hs. Choose 1 to represent H in S. Cosets partition G, and cancellation shows that multiplication gives bijections T × H → G and H × S → G: existence follows from the coset descriptions, and equality first identifies the coset representative and then the H factor. Thus |T| = d. Inversion identifies left and right cosets, so |S| = d as well.
2. For L = G or H, let B(L)_m be the free k-module on tuples (g₀,…,g_m) in L, with diagonal left L-action. For m ≥ 1 define ∂_m by the alternating sum of vertex deletions, and set ∂₀ = 0. Deletion commutes with the action. The differential squares to zero: deleting original positions i < j in the two orders gives the same tuple with signs (−1)^{i+j−1} and (−1)^{i+j}, so these terms cancel. The composite involving ∂₀ is zero by definition. Hence equivariant linear maps B(L)_m → A form a cochain complex with differential given by precomposition with ∂_{m+1}.
3. Identify this cochain complex with the inhomogeneous complex defining groupCohomology. An equivariant cochain F corresponds to f(x₁,…,x_m) = F(1,x₁,x₁x₂,…,x₁⋯x_m). Conversely define F(g₀,…,g_m) = g₀ f(g₀⁻¹g₁,g₁⁻¹g₂,…,g_{m−1}⁻¹g_m), and extend linearly from the free basis. Simultaneous left translation preserves adjacent ratios and multiplies the value by the translating element, proving equivariance. Substitution proves that the formulas are inverse. Deleting the first vertex produces x₁f(x₂,…,x_{m+1}); deleting an interior vertex multiplies the adjacent ratios; deleting the last drops the last ratio. The differential is therefore x₁f(x₂,…,x_{m+1}) + Σ_{i=1}^m (−1)^i f(x₁,…,x_i x_{i+1},…,x_{m+1}) + (−1)^{m+1}f(x₁,…,x_m), exactly the pinned inhomogeneous differential. Empty tuples give the same identification in degree zero. All maps are k-linear.
4. For g = hs in the unique decomposition given by S, define r(g) = h, and let i : H → G be inclusion. Uniqueness gives r(hg) = h r(g). Since S represents H by 1, r(h) = h. Applying r and i coordinatewise gives H-equivariant chain maps r_* : B(G) → B(H) and i_* : B(H) → B(G); they commute with every deletion and satisfy r_*i_* = id.
5. Write u = id_G and v = i ∘ r. On a basis tuple define D_m(g₀,…,g_m) = Σ_{j=0}^m (−1)^j(ug₀,…,ug_j,vg_j,…,vg_m), extending linearly, and set D_{−1} = 0. These maps are H-equivariant. They satisfy ∂D + D∂ = v_* − u_*. Indeed, in the jth prism summand, deletion of position k < j cancels the term obtained by first deleting g_k and then using prism position j−1; the signs are (−1)^{j+k} and (−1)^{j+k−1}. Deletion of k > j+1 cancels the term obtained by first deleting g_{k−1} and using prism position j, with the same opposite signs. These pairings account for every term of D∂. The two remaining deletions give +(ug₀,…,ug_{j−1},vg_j,…,vg_m) and −(ug₀,…,ug_j,vg_{j+1},…,vg_m). Their sum over j telescopes to the all-v tuple minus the all-u tuple. This also proves the formula for m = 0.
6. Precomposition with i_* and r_* induces inverse maps on cohomology between Hom_H(B(G),A) and Hom_H(B(H),A). One composite is already the identity. For the other, if F is a degree-m cocycle, then F(v_*−u_*) = F∂D + FD∂ = FD∂. For m ≥ 1 this is the coboundary of F D_{m−1}; for m = 0 it is zero because D_{−1} = 0. Precomposition preserves cocycles and coboundaries since the original maps are chain maps. Therefore, together with step 3, there is a k-linear isomorphism α from the degree-n cohomology of Hom_H(B(G),A) to Hⁿ(H,Res_H A), with inverse β. Step 3 also gives a k-linear isomorphism γ from Hⁿ(G,A) to the degree-n cohomology of Hom_G(B(G),A).
7. On the common complex B(G), define R_c by forgetting part of the equivariance. For an H-equivariant cochain F define (C_c F)(b) = Σ_{t∈T} t F(t⁻¹b). Each summand is unchanged if t is replaced by th with h ∈ H, because th F(h⁻¹t⁻¹b) = t F(t⁻¹b). Thus the sum is independent of the chosen representatives. For g ∈ G, the set gT is another left transversal, and evaluation using it gives (C_c F)(gb) = Σ_t gt F(t⁻¹b) = g(C_c F)(b). Consequently C_c F is G-equivariant. Both maps are k-linear.
8. Equivariance of ∂ gives C_c(F ∘ ∂) = (C_c F) ∘ ∂; restriction also commutes with the differential. Hence these maps induce k-linear cohomology maps, denoted R̄ and C̄. For a G-equivariant F, each summand t F(t⁻¹b) is F(b), so C_c R_c F = d • F. Passing to cohomology gives C̄R̄ = d • id, because cocycles and coboundaries are preserved and the quotient map is additive.
9. Define R = α R̄ γ and C = γ⁻¹ C̄ β. Since βα = id, their composite is γ⁻¹ C̄R̄ γ = γ⁻¹(d • id)γ. The isomorphism γ and its inverse are additive, so this composite sends every x to d • x. These are the required maps.

## Key steps

1. Choose left and right transversals and identify their cardinality with the subgroup index.
2. Identify homogeneous equivariant cochains with the pinned inhomogeneous cochains.
3. Construct the H-equivariant retraction and verify the prism homotopy.
4. Obtain inverse cohomology maps allowing H-cohomology to be computed on B(G).
5. Define coset-sum corestriction and prove its composite with restriction is the index action.
6. Transport the maps through the linear cohomology identifications.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/610

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
