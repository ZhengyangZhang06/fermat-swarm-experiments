<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1 -->

## Theorem `Submission.p04_hct139_coset_average_exists`

Let k be a commutative ring, G a group equipped with Fintype G, and A and B k-linear G-representations in the same representation universe. Let H ≤ G have Fintype H, and equip the set Q = G/H of left cosets with a Fintype structure. For q ∈ Q, write t_q = Quotient.out q. There exists a k-linear map C : Hom_H(Res_H B, Res_H A) → Hom_G(B,A) such that, for every H-equivariant k-linear map F and every x ∈ B, (C F)(x) = Σ_{q∈Q} ρ_A(t_q)(F(ρ_B(t_q⁻¹)(x))). No normality of H or finiteness or projectivity of A or B is assumed.

Node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/139

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/152, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/153

## Lean problem

Declaration: `Submission.p04_hct139_coset_average_exists`

```lean
∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A B : Rep k G) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)], ∃ C : (Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) →ₗ[k] (Quiver.Hom B A), ∀ (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (x : B), (C F).hom x = ∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))
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

- Parent DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1`
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data and write Q = G/H. For each q ∈ Q set t_q = Quotient.out q, so t_q represents q. For an H-equivariant k-linear map F and t ∈ G, define L_t(F)(x) = ρ_A(t)(F(ρ_B(t⁻¹)(x))). Define S_F(x) = Σ_{q∈Q} L_{t_q}(F)(x). This is a finite sum by the supplied Fintype structure on Q.
2. Each L_t(F) is k-linear in x, being a composition of three k-linear maps. Consequently S_F(x+y) = S_F(x)+S_F(y) and S_F(a x) = a S_F(x) for all x,y ∈ B and a ∈ k. Thus S_F is a k-linear map B → A.
3. For h ∈ H, the representation multiplication laws and H-equivariance of F give L_{th}(F)(x) = ρ_A(t)ρ_A(h)F(ρ_B(h⁻¹)ρ_B(t⁻¹)x) = ρ_A(t)ρ_A(h)ρ_A(h⁻¹)F(ρ_B(t⁻¹)x) = L_t(F)(x). Therefore L_t(F) depends only on the left coset tH: if t'H=tH, then t'=th for some h ∈ H, and the preceding equality applies.
4. Fix g ∈ G. Left multiplication induces a permutation q ↦ gq of Q, with inverse q ↦ g⁻¹q. The representatives t_{gq} and gt_q represent the same left coset. Step 3 therefore gives L_{t_{gq}}(F) = L_{gt_q}(F). Furthermore, for x ∈ B, L_{gt_q}(F)(ρ_B(g)x) = ρ_A(g)ρ_A(t_q)F(ρ_B(t_q⁻¹)ρ_B(g⁻¹)ρ_B(g)x) = ρ_A(g)L_{t_q}(F)(x).
5. Reindexing the finite sum by q ↦ gq and applying step 4 yields S_F(ρ_B(g)x) = Σ_q L_{t_{gq}}(F)(ρ_B(g)x) = Σ_q ρ_A(g)L_{t_q}(F)(x) = ρ_A(g)S_F(x). The last equality uses linearity of ρ_A(g). Hence S_F is G-equivariant and defines an element C(F) of Hom_G(B,A).
6. For H-equivariant maps F₁,F₂, evaluation of the formula gives L_t(F₁+F₂)(x) = L_t(F₁)(x)+L_t(F₂)(x). For a ∈ k it gives L_t(aF₁)(x) = aL_t(F₁)(x). Finite summation and extensionality therefore give C(F₁+F₂)=C(F₁)+C(F₂) and C(aF₁)=aC(F₁). Thus C is k-linear between the stated Hom modules.
7. By its construction, C satisfies (C F)(x)=Σ_{q∈Q}ρ_A(t_q)(F(ρ_B(t_q⁻¹)x)) for every F and x. This is precisely the required formula and completes the existence proof.

## Key steps

1. Define the finite coset sum using Quotient.out representatives.
2. Show each summand and the sum are linear in the input vector.
3. Use H-equivariance to prove invariance under replacing t by th.
4. Reindex left cosets by multiplication by g to establish G-equivariance.
5. Show addition and scalar multiplication of F pass through the sum.
6. Package the resulting maps as a linear operator with the required formula.

## Reference use

### local-project

Queries:
- `linearYonedaObj|transversal|cores|transfer|restriction|Hom_G`
- `linearYonedaObj`
- `def res|resFunctor|res_map|map_hom|hom_comm_apply|ofHom`
- `coset.*[Aa]verag|[Aa]verag.*coset|[Hh]om.*[Tt]ransfer|[Tt]ransfer.*[Hh]om`
- `p04_hct139_coset_average_exists|p04_hct139_coset_average_laws`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions/Def_GroupCohomology_TateCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Coset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Coset/Card.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Index.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/CategoryTheory/Abelian/Ext.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/tmp/p04_hom_split_7lyjeeym/Check.lean`
- `/tmp/p04_hom_split_7lyjeeym/check.log`

The manifest pins project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Rep/Basic supplies equivariant Hom modules, pointwise nsmul, and hom_comm_apply; Rep/Res shows restriction retains underlying linear maps and is linear. Coset/Card supplies quotient finiteness, Index defines H.index as Nat.card (G ⧸ H), and Abelian/Ext defines linearYonedaObj with Hom modules in each degree. The targeted averaging/transfer-name search found no relevant match. Neither proposed identifier occurs in the inspected DAG, node contracts, or Submission source. The consulted mathlib files match the installed pinned sources byte for byte. Lean 4.33.1 elaborated both proposed types after import Submission using the available compiled Submission module; anonymous rfl checks verified restriction and Hom nsmul semantics. Axiom checks for Rep.resMap, Rep.hom_comm_apply, Subgroup.index_eq_card, and ChainComplex.linearYonedaObj reported only propext, Classical.choice, and Quot.sound. These interface checks do not constitute comparator acceptance of either child.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/377

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
