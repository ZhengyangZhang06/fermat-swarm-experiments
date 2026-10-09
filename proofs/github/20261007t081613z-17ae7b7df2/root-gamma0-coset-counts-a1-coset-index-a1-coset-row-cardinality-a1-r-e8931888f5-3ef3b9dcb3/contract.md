<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1.row_quotient_equality-a1 -->

## Theorem `Submission.p10_17ae7b7d_crcard_quot_eq_unit`

Let R be a commutative ring, with no nontriviality assumption. Define U={(r,s)∈R² | ∃x,y∈R, xr+ys=1}. For v,w∈U, define rel(v,w) to mean that there exists u∈R× with uv₁=w₁ and uv₂=w₂. Then for every v,w∈U, their images in Quot rel are equal if and only if rel(v,w).

Node: `root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1.row_quotient_equality-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/464

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_crcard_quot_eq_unit`

```lean
∀ (R : Type) [CommRing R], let U := {v : R × R // ∃ x y : R, x * v.1 + y * v.2 = 1}; let rel : U → U → Prop := fun v w => ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2; ∀ v w : U, Quot.mk rel v = Quot.mk rel w ↔ rel v w
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

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1.row_quotient_equality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a commutative ring R. Let U be the stated unimodular-row subtype and let rel be unit scaling. If xr+ys=1 and u is a unit, then (x u⁻¹)(ur)+(y u⁻¹)(us)=xr+ys=1, so scaling preserves U.
2. The unit 1 scales every row to itself. If u scales v to w, then u⁻¹ scales w to v, since u⁻¹(ur)=r in each coordinate. If u scales v to w and t scales w to z, then the unit tu scales v to z, by associativity in each coordinate. Thus rel is reflexive, symmetric and transitive.
3. Equality of the images of v and w in Quot rel is equivalent to membership in the equivalence relation generated by rel. Every generator is rel-related; reflexivity, symmetry and transitivity from step 2 show, by induction on the generation of this relation, that every generated pair is already rel-related. Conversely every rel-related pair is a generator and has equal quotient images. Hence Quot.mk rel v = Quot.mk rel w if and only if rel v w, which is precisely the existence of the stated scaling unit. No nontriviality assumption on R is used.

## Key steps

1. Unit scaling preserves unimodularity by scaling the witness coefficients by the inverse unit.
2. Identity, inverse and product units establish reflexivity, symmetry and transitivity.
3. The generated equivalence relation therefore equals unit scaling, giving the exact quotient-equality criterion.

## Reference use

### local-project

Queries:
- `unimodularRow|ProjectiveLine|Gamma0|rightRel|leftRel`
- `quot.*(eq|equiv)|eq.*quot|Quot.eq|EqvGen|SL2_inv_expl|det_coe|det_fin_two`
- `Gamma0.*(row|equiv)|bottomRow|bottom_row|row.*Gamma0`
- `p10_17ae7b7d_crcard_(quot_eq_unit|gamma0_row_criterion)`
- `python3 /tmp/p10_coset_split_diagnostics.py`
- `python3 /tmp/p10_coset_split_retry.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Quot.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Logic/Relation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/coset-row-split-m1rrb_86/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/coset-row-split-m1rrb_86/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/coset-row-split-m1rrb_86/TargetAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/coset-row-split-m1rrb_86/report.json`

The snapshot matches project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; both snapshot trees and all nine pinned dependency checkouts had clean tracked files. The projective-line source supplies the unit-scaling equivalence argument, but that module is outside the frozen imports, so the proposed interface uses the explicit subtype and Quot. Mathlib supplies Equivalence.quot_mk_eq_iff, Gamma0_mem, determinant-one and inverse-matrix formulas, and quotientRightRelEquivQuotientLeftRel. The focused search found no existing bottom-row Gamma0 criterion in project Definitions or mathlib ModularForms. Neither proposed identifier was reserved in the searched DAGs or handoffs. Both exact child types compiled after import Submission in a disposable captured compiler copy. A reflexivity check identified special-linear multiplication with the explicit finite-sum matrix product. The types and checked library declarations use only propext, Classical.choice and Quot.sound, or no axioms. The matching header policy digest is 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; only lines 10–12 were omitted, and Lean checked all 56 targets absent. The receipt records exact omitted text, reversible copies, contract original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and compiler-copy hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539. No production source was edited by these diagnostics; a concurrent Submission update was recorded and preserved. These are interface checks, not comparator acceptance of proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
