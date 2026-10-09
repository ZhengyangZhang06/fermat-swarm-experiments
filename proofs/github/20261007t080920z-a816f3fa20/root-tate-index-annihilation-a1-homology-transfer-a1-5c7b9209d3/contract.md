<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.homology_transfer-a1 -->

## Theorem `Submission.p04_tia_homology_transfer`

Let k be a commutative ring, G a group with a finite-type structure, A a k-linear G-representation, H a subgroup equipped with a finite-type structure, and n a natural number. Use the common universe required by groupHomology. There exist k-linear maps T : Hₙ(G,A) → Hₙ(H,Res_H A) and P : Hₙ(H,Res_H A) → Hₙ(G,A) such that P(T(x)) = [G:H] • x for every x, where • is repeated addition. No normality of H or finiteness of A is assumed.

Node: `root.tate_index_annihilation-a1.homology_transfer-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/21

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/136, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/137

## Lean problem

Declaration: `Submission.p04_tia_homology_transfer`

```lean
∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ), ∃ T : groupHomology A n →ₗ[k] groupHomology (Rep.res H.subtype A) n, ∃ P : groupHomology (Rep.res H.subtype A) n →ₗ[k] groupHomology A n, ∀ x : groupHomology A n, P (T x) = H.index • x
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
- Child DAG node: `root.tate_index_annihilation-a1.homology_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the hypotheses and put d = [G:H]. Choose a right transversal S, representing each right coset Hs exactly once, with representative 1 for H. Every g has a unique expression hs: equality of two such expressions identifies the coset representatives, after which cancellation identifies h. Thus H × S → G is a bijection. Inversion bijects right and left cosets, so |S| = d.
2. For L = G or H, let B(L)_m be the free k-module on tuples (g₀,…,g_m) in L with diagonal left action. Give it the alternating vertex-deletion boundary for m ≥ 1 and zero boundary in degree zero. These maps are equivariant. Deleting original positions i < j in the two orders yields opposite signs (−1)^{i+j−1} and (−1)^{i+j}, proving ∂² = 0; the composite involving the degree-zero boundary is zero by definition. Tensor with A over k, give the tensor product the diagonal action, and take L-coinvariants. Equivariance ensures that the boundary descends.
3. Identify (A ⊗_k B(L)_m)_L with the inhomogeneous chains defining groupHomology. Send [a ⊗ (g₀,…,g_m)]_L to the chain with coefficient g₀⁻¹a at (g₀⁻¹g₁,…,g_{m−1}⁻¹g_m). The formula is linear in a and in the free-module variable, so it respects tensor relations. Simultaneously translating a and the vertices by l preserves the coefficient, since (lg₀)⁻¹(la) = g₀⁻¹a, and preserves all adjacent ratios. Thus it respects coinvariants. Its inverse sends a[x₁,…,x_m] to [a ⊗ (1,x₁,x₁x₂,…,x₁⋯x_m)]_L and extends over finitely supported sums. One composite is immediate; the other equals the identity because simultaneous translation by g₀⁻¹ normalizes the first vertex to 1. On a normalized representative the boundary is (x₁⁻¹a)[x₂,…,x_m] + Σ_{i=1}^{m−1}(−1)^i a[x₁,…,x_i x_{i+1},…,x_m] + (−1)^m a[x₁,…,x_{m−1}]. This agrees with the pinned inhomogeneous boundary, including its inverse action. Both degree-zero boundaries are zero. Hence these are k-linear chain isomorphisms.
4. Define r : G → H by r(hs) = h and let i : H → G be inclusion. Uniqueness of the right-coset decomposition gives r(hg) = h r(g), and the choice of representative 1 gives r(h) = h. Coordinatewise application produces H-equivariant chain maps r_* and i_* between B(G) and B(H), with r_*i_* = id, because coordinatewise maps commute with deletion.
5. Set u = id_G and v = i ∘ r. Define D_m(g₀,…,g_m) = Σ_{j=0}^m (−1)^j(ug₀,…,ug_j,vg_j,…,vg_m), extending linearly, and set D_{−1} = 0. The maps are H-equivariant and satisfy ∂D + D∂ = v_* − id. To verify this, deleting position k < j in the jth prism term cancels first deleting g_k and taking prism position j−1: the signs are (−1)^{j+k} and (−1)^{j+k−1}. Deleting k > j+1 cancels first deleting g_{k−1} and taking prism position j, again with opposite signs. Every term in D∂ is paired this way. The remaining deletions in prism term j are +(ug₀,…,ug_{j−1},vg_j,…,vg_m) and −(ug₀,…,ug_j,vg_{j+1},…,vg_m); these telescope to the all-v tuple minus the original tuple. The same calculation covers m = 0.
6. Tensor i_*, r_*, and D with the identity of A and pass to H-coinvariants, which is legitimate by their H-equivariance. The homotopy identity is preserved. On a cycle z, the difference between the endomorphism induced by i_*r_* and the identity is ∂Dz, a boundary. Thus the induced homology maps from r_* and i_* are inverse; the other composite was already the identity on chains. Combining this with step 3 yields a k-linear isomorphism α from Hₙ((A ⊗ B(G))_H) to Hₙ(H,Res_H A), with inverse β. Step 3 gives a k-linear isomorphism γ from Hₙ(G,A) to Hₙ((A ⊗ B(G))_G).
7. For any k-linear G-representation W, write W_L for the quotient by the k-span of lw−w with l ∈ L. Define π_W : W_H → W_G by [w]_H ↦ [w]_G. This is well-defined because every H-relation is a G-relation. Define a linear map W → W_H by w ↦ Σ_{s∈S}[sw]_H. Replacing s by hs leaves its term unchanged. For g ∈ G, right multiplication changes S into another right transversal Sg, so representative independence and permutation of the finite right-coset set give Σ_s[sgw]_H = Σ_s[sw]_H. The map therefore kills each gw−w and its k-span, inducing τ_W : W_G → W_H. For every representative w, π_Wτ_W([w]_G) = Σ_s[sw]_G = d • [w]_G. Every class has a representative, so π_Wτ_W = d • id.
8. Apply step 7 to W_m = A ⊗_k B(G)_m. Its boundary is k-linear and G-equivariant. It commutes with π because both induced quotient maps send a representative to its boundary class, and it commutes with τ because ∂(sw) = s∂w and ∂ preserves finite sums. Consequently π and τ are chain maps with composite d • id. They induce k-linear maps π̄ and τ̄ on homology: cycles map to cycles and boundaries to boundaries. Their composite sends the class of a cycle z to the class of d • z, hence equals d • id.
9. Set T = α τ̄ γ and P = γ⁻¹ π̄ β. Since βα = id, the composite is γ⁻¹ π̄τ̄ γ = γ⁻¹(d • id)γ. Additivity of γ and its inverse makes this d • id on Hₙ(G,A). This proves the required statement, including n = 0.

## Key steps

1. Choose a right transversal with cardinality equal to the index.
2. Identify tensor coinvariants of the homogeneous complex with the pinned inhomogeneous chains.
3. Use the equivariant retraction and explicit prism homotopy to compute H-homology on B(G).
4. Construct coinvariant projection and transfer and prove their composite is the index action.
5. Apply these maps degreewise and descend to homology.
6. Transport through the linear homology identifications.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/477

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
