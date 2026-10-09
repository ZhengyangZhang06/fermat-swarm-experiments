<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1.finite_product_row_classes-a1 -->

## Theorem `Submission.p10_17ae7b7d_crt_pi_rows`

Let I be any finite index type, possibly empty, and let R_i be a commutative ring for each i∈I. For each commutative ring A, let P(A) be the quotient of {(r,s)∈A² | ∃x,y∈A, xr+ys=1} by simultaneous multiplication of both coordinates by one unit of A. Equip T=∏_{i∈I}R_i with its pointwise commutative-ring structure. Then there exists an equivalence P(T)≃∏_{i∈I}P(R_i). The component rings need not be finite or nontrivial.

Node: `root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1.finite_product_row_classes-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/466

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_crt_pi_rows`

```lean
∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)], let P := fun (A : Type) [CommRing A] => Quot (fun v w : {v : A × A // ∃ x y : A, x * v.1 + y * v.2 = 1} => ∃ u : Aˣ, (u : A) * v.1.1 = w.1.1 ∧ (u : A) * v.1.2 = w.1.2); Nonempty (P (∀ i, R i) ≃ (∀ i, P (R i)))
```

### Frozen project context

`Fermat/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean` at `a97febc53b1c4d489edc54ca44132af7a21279b3` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.CuspSpace.cuspDenomAux_infty
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one

set_option autoImplicit false

theorem CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero (N : ℕ) [NeZero N]
    (hg : ModularCurve.genusFormula N = 0) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f = 0 := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1.finite_product_row_classes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let I be the given finite index type, let R_i be the given commutative rings, and let T=∏_i R_i with pointwise operations. For any commutative ring A define U(A) to be its unimodular pairs and P(A) to be the displayed Quot. Multiplying a unimodular pair with witnesses x,y by a unit u preserves unimodularity using witnesses x*u^{-1}, y*u^{-1}. Unit scaling is reflexive, symmetric, and transitive, witnessed respectively by 1, u^{-1}, and products of scaling units. Consequently two representative rows have equal classes in P(A) exactly when one scaling unit takes the first row to the second.
2. If (r,s) is a row in U(T) with witnesses x,y, then evaluating xr+ys=1 at i yields x_i*r_i+y_i*s_i=1. Send its class to the tuple of classes [(r_i,s_i)]. If a unit u of T scales one global row to another, evaluation of u and its inverse gives a unit u_i in R_i scaling the component rows. Hence this assignment is independent of representatives and defines F:P(T)→∏_i P(R_i).
3. For surjectivity, fix a tuple of classes q_i. Choose for each i a representative (r_i,s_i) and witnesses x_i,y_i satisfying x_i*r_i+y_i*s_i=1. These choices exist because each quotient class has a representative and each representative is unimodular. Define r,s,x,y in T by these component values. Function extensionality gives xr+ys=1, so (r,s) is a unimodular global row. Its class maps to q_i for every i and therefore to the prescribed tuple.
4. For injectivity, choose representative global rows (r,s) and (r',s') for two classes having the same F-image. For each i their component classes agree. By the equivalence-relation characterization in step 1 there is a unit u_i in R_i with u_i*r_i=r'_i and u_i*s_i=s'_i. Choose such a unit for every i.
5. Define a in T by a_i=u_i and b in T by b_i=u_i^{-1}. The equations a_i*b_i=b_i*a_i=1 hold for every i, so pointwise multiplication and extensionality give ab=ba=1 in T. Thus a is the value of a unit u of T with inverse value b. The component scaling equations yield u*r=r' and u*s=s' by extensionality. The global rows are related, so their quotient classes are equal. This proves injectivity.
6. A bijection F yields an equivalence by assigning to each target its unique preimage. Surjectivity supplies a preimage, and injectivity makes both inverse identities hold. Therefore P(T)≃∏_i P(R_i) is nonempty. All component choices and extensional equalities above also apply when I is empty: there is exactly one empty function, all displayed pointwise equations are vacuous, and the same constructions and inverse identities remain valid.

## Key steps

1. Identify quotient equality with simultaneous unit scaling.
2. Evaluate global rows, witnesses and units componentwise to define the quotient map.
3. Assemble representatives and unimodularity witnesses to prove surjectivity.
4. Extract component scaling units from equality of component classes.
5. Assemble those units and their inverses into one global unit to prove injectivity.
6. Turn the bijection into an equivalence, including the empty-index case.

## Reference use

### local-project

Queries:
- `ProjectiveLine|UnimodularRow|unimodularRow|chineseRemainder|primeFactors`
- `chineseRemainder|primeFactors|factorization`
- `(ProjectiveLine|UnimodularRow).*(equiv|Equiv|prod|Pi)|(equiv|Equiv|prod|Pi).*(ProjectiveLine|UnimodularRow)`
- `card_pi|card_congr|finite_quot|finite_quotient`
- `prod_coe_sort|prod_attach|prod_subtype`
- `p10_17ae7b7d_crt_ring_equiv_rows|p10_17ae7b7d_crt_pi_rows`
- `python3 /tmp/p10_crt_split_diagnostic.py`
- `python3 /tmp/p10_crt_refine_types.py`
- `python3 /tmp/p10_crt_parent_assembly.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/QuotientRing.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Quot.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/SetTheory/Cardinal/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/crt-split-95f4i2pe/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/crt-split-95f4i2pe/ParentAssembly.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/crt-split-95f4i2pe/report.json`

The clean snapshots match project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine pinned dependency checkouts were also clean and matched their revisions. The project defines the same unit-scaling quotient and its ring-homomorphism map, but that module is outside the frozen imports, so the child types retain explicit Quot expressions. No corresponding project ring-isomorphism or product-equivalence theorem was found; the targeted search matched only unrelated names sharing header lines. ZMod.equivPi supplies the required CRT isomorphism, while Equivalence.quot_mk_eq_iff, Nat.card_congr, Nat.card_pi and Finset.prod_coe_sort supply quotient equality and cardinality infrastructure. Both proposed names are absent from Submission, the DAG and node metadata. Both final types compiled without warnings after import Submission. Reflexivity checks verified pointwise product-ring multiplication, addition and one, and multiplication of unit values. A conditional Lean proof assembled the exact frozen parent type from these two interfaces. Checked types and library results use only propext, Classical.choice and Quot.sound. The disposable compiler copy followed policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: only lines 10–12 were omitted, and Lean confirmed all 56 targets absent. The report records exact omitted text, reversible original/build hashes and probe evidence. Frozen sources and handoffs were unchanged. These are interface diagnostics, not comparator acceptance of either child proof.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
