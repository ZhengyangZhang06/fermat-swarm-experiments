<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_laws-a1 -->

## Theorem `Submission.p04_hct139_coset_average_laws`

Let k be a commutative ring, G a group with Fintype G, A a k-linear G-representation, and H ≤ G with Fintype H and Fintype(G/H). All representations below lie in the same representation universe as A. Suppose a family of k-linear maps C_B : Hom_H(Res_H B, Res_H A) → Hom_G(B,A), indexed by all such G-representations B, satisfies (C_B F)(x) = Σ_{q∈G/H} ρ_A(t_q)(F(ρ_B(t_q⁻¹)x)), where t_q = Quotient.out q. Then, for every G-equivariant k-linear map f : D → B and H-equivariant k-linear map F : Res_H B → Res_H A, C_D(F ∘ Res_H f) = (C_B F) ∘ f. Moreover, for every G-equivariant k-linear map E : B → A, C_B(Res_H E) = H.index • E, where • is repeated addition of equivariant maps. No normality or finiteness or projectivity of the representations is assumed.

Node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_laws-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/139

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p04_hct139_coset_average_laws`

```lean
∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)] (C : ∀ B : Rep k G, (Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) →ₗ[k] (Quiver.Hom B A)), (∀ (B : Rep k G) (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (x : B), (C B F).hom x = ∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))) → (∀ (B D : Rep k G) (f : Quiver.Hom D B) (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)), C D (CategoryTheory.CategoryStruct.comp ((Rep.resFunctor H.subtype).map f) F) = CategoryTheory.CategoryStruct.comp f (C B F)) ∧ (∀ (B : Rep k G) (F : Quiver.Hom B A), C B ((Rep.resFunctor H.subtype).map F) = H.index • F)
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
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_laws-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data, the family C, and its assumed formula. Write Q = G/H and t_q = Quotient.out q. Restriction of a representation morphism retains its underlying k-linear map, and composition of representation morphisms is ordinary composition of those maps.
2. Fix B,D, a G-equivariant map f : D → B, an H-equivariant map F : Res_H B → Res_H A, and x ∈ D. Equivariance of f gives f(ρ_D(t_q⁻¹)x)=ρ_B(t_q⁻¹)f(x) for every q ∈ Q. Applying the assumed formula to the composite F ∘ Res_H f therefore gives (C_D(F ∘ Res_H f))(x) = Σ_q ρ_A(t_q)F(f(ρ_D(t_q⁻¹)x)) = Σ_q ρ_A(t_q)F(ρ_B(t_q⁻¹)f(x)).
3. The last sum in step 2 equals (C_B F)(f(x)) by the assumed formula for C_B. Equality for every x gives C_D(F ∘ Res_H f) = (C_B F) ∘ f by extensionality of equivariant linear maps. Since B,D,f,F were arbitrary, this proves the first universally quantified conclusion.
4. Fix a representation B, a G-equivariant k-linear map E : B → A, and x ∈ B. For each q ∈ Q, G-equivariance gives E(ρ_B(t_q⁻¹)x)=ρ_A(t_q⁻¹)E(x). Hence the q-th summand in the formula for C_B(Res_H E)(x) equals ρ_A(t_q)ρ_A(t_q⁻¹)E(x)=E(x), using the representation laws and t_q t_q⁻¹=1.
5. It follows that (C_B(Res_H E))(x)=Σ_{q∈Q}E(x)=Fintype.card(Q) • E(x). Because Q is finite, Fintype.card(Q)=Nat.card(Q), and by definition Nat.card(Q)=H.index. Thus (C_B(Res_H E))(x)=H.index • E(x).
6. Natural-number scalar multiplication on representation morphisms is pointwise repeated addition, so the right side of step 5 is the value of H.index • E at x. Extensionality yields C_B(Res_H E)=H.index • E. Since B and E were arbitrary, this proves the second universally quantified conclusion. Pairing it with step 3 proves the required conjunction.

## Key steps

1. Use that restriction preserves underlying maps and composition.
2. Move precomposition by a G-equivariant map through each averaging summand.
3. Apply the assumed formula and extensionality to obtain naturality.
4. Use full G-equivariance to make every summand of a restricted map equal that map.
5. Identify the number of left cosets with H.index.
6. Use pointwise nsmul and extensionality to obtain the index identity.

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

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/293

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
