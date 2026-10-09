<!-- theorem-id: fermat-p04/root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1 -->

## Theorem `Submission.p04_prism_a8325b9888_boundary_identity`

Let k be a commutative ring and X a type in the same universe, and let u,v : X → X be arbitrary functions. Write [c]=MonoidAlgebra.single c 1. Define Pₘ(c)=Σⱼ₌₀ᵐ (−1)ʲ[uc₀,…,ucⱼ,vcⱼ,…,vcₘ], with the j-th tuple precisely Fin.insertNth j.castSucc (u(c j)) (fun i => if i<j then u(c i) else v(c i)). For r≥1, let ∂ᵣ=Rep.standardComplex.d k X r, the k-linear alternating-deletion map on (r+1)-tuples, and let δ_b c=c ∘ b.succAbove. Then ∂₁P₀(c)=[v∘c]−[u∘c] for every one-entry tuple c. Moreover, for every n≥0 and c : Fin(n+2) → X, ∂ₙ₊₂Pₙ₊₁(c)+Σ_b∈Fin(n+2) (−1)ᵇPₙ(δ_b c)=[v∘c]−[u∘c]. No group structure or equivariance hypothesis on X, u, or v is required.

Node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/149

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/167, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/168

## Lean problem

Declaration: `Submission.p04_prism_a8325b9888_boundary_identity`

```lean
∀ {k X : Type _} [CommRing k] (u v : X → X), let P : ∀ n : ℕ, (Fin (n + 1) → X) → MonoidAlgebra k (Fin (n + 2) → X) := fun n c => ∑ j : Fin (n + 1), MonoidAlgebra.single (Fin.insertNth j.castSucc (u (c j)) (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i))) ((-1 : k) ^ j.val); (∀ c : Fin 1 → X, Rep.standardComplex.d k X 1 (P 0 c) = MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k)) ∧ ∀ (n : ℕ) (c : Fin (n + 2) → X), Rep.standardComplex.d k X (n + 2) (P (n + 1) c) + ∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove) = MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k)
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
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, X, u and v. Denote the j-th prism tuple of a degree-m tuple c by Qₘ,ⱼ(c). Inserting u(c j) at position j into the tuple whose entries are u(c i) for i<j and v(c i) for i≥j gives exactly (uc₀,…,ucⱼ,vcⱼ,…,vcₘ). Thus the Lean definition of P is Σⱼ(−1)ʲ[Qₘ,ⱼ(c)]. The map ∂ᵣ is k-linear and satisfies ∂ᵣ[t]=Σₐ₌₀ʳ(−1)ᵃ[δₐt], by its defining alternating-deletion formula.
2. If c has one entry x, then P₀(c)=[ux,vx]. Its boundary is [vx]−[ux], proving the degree-zero assertion, including its stated sign.
3. For the positive-degree assertion, first fix any N≥1 and c=(x₀,…,x_N). Expand ∂ₙ with N as the degree: specifically, ∂_{N+1}P_N(c) is the sum indexed by 0≤j≤N and 0≤a≤N+1 whose term is (−1)^{j+a}[δₐQ_{N,j}(c)]. The second expression Σ_b(−1)ᵇP_{N−1}(δ_b c) is the sum indexed by 0≤b≤N and 0≤t≤N−1 whose term is (−1)^{b+t}[Q_{N−1,t}(δ_b c)]. These expansions follow from linearity and multiplication of powers of −1.
4. Suppose a<j in the first sum. Deleting position a removes u(x_a) before the transition. The resulting tuple is Q_{N−1,j−1}(δ_a c): deleting original vertex a shifts the transition vertex x_j to position j−1 and preserves every other entry in order. The matching term in the second sum has b=a and t=j−1, with coefficient (−1)^{a+j−1}. This coefficient is the additive inverse of (−1)^{j+a}, so the paired terms sum to zero.
5. Suppose a>j+1 in the first sum. Deleting position a removes v(x_{a−1}) after the transition. The resulting tuple is Q_{N−1,j}(δ_{a−1}c): deletion occurs after x_j and leaves its transition position unchanged. Here j≤N−1 follows from a≤N+1 and a>j+1. The matching second-sum term has b=a−1 and t=j, with coefficient (−1)^{a−1+j}, again the additive inverse of (−1)^{j+a}.
6. Every second-sum term has exactly one of these pairings. If b≤t, take j=t+1 and a=b; these satisfy a<j and recover step 4. If b>t, take j=t and a=b+1; these satisfy a>j+1 and recover step 5. These cases are disjoint and exhaustive, and their formulas invert the pairings in steps 4 and 5. Thus all second-sum terms cancel with exactly the noncentral first-sum terms. This is cancellation of indexed terms, so it does not require distinct tuples or injectivity of either function.
7. The remaining first-sum terms have a=j or a=j+1. For a=j the coefficient is (−1)^{2j}=1 and the tuple is A_j=(ux₀,…,ux_{j−1},vx_j,…,vx_N). For a=j+1 the coefficient is (−1)^{2j+1}=−1 and the tuple is B_j=(ux₀,…,ux_j,vx_{j+1},…,vx_N). For j<N, B_j=A_{j+1}; hence Σ_{j=0}^N([A_j]−[B_j])=[A₀]−[B_N]=[v∘c]−[u∘c]. Combined with step 6, this proves ∂_{N+1}P_N(c)+Σ_b(−1)ᵇP_{N−1}(δ_b c)=[v∘c]−[u∘c].
8. Given n in the stated positive-degree formula, put N=n+1. Then c has N+1=n+2 entries, ∂_{N+1}=∂_{n+2}, and P_{N−1}=P_n. Step 7 is exactly the required formula. Together with step 2, it proves both conjuncts.

## Key steps

1. Identify the inserted tuples and expand the alternating differential.
2. Compute the degree-zero boundary directly.
3. Cancel deletions before the transition against the preceding prism position.
4. Cancel deletions after the transition against the unchanged prism position.
5. Prove the two pairings exhaust the lower-degree prism sum.
6. Telescope the two central deletions to the v-endpoint minus the u-endpoint.
7. Substitute N=n+1 to obtain the exact positive-degree formula.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/499

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
