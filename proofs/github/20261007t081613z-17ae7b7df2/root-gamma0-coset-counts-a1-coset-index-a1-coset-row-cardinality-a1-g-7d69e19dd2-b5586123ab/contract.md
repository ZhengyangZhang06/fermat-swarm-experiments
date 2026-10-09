<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1.gamma0_bottom_row_criterion-a1 -->

## Theorem `Submission.p10_17ae7b7d_crcard_gamma0_row_criterion`

Let N be a nonzero natural number, put R=ℤ/Nℤ, and let A,B∈SL₂(ℤ). Define Γ₀(N) as the subgroup whose bottom-left entry reduces to zero in R. Then BA⁻¹∈Γ₀(N) if and only if there exists a unit u∈R× such that u times the reduction of A₂₁ equals the reduction of B₂₁, and u times the reduction of A₂₂ equals the reduction of B₂₂.

Node: `root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1.gamma0_bottom_row_criterion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/464

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_crcard_gamma0_row_criterion`

```lean
∀ (N : ℕ) [NeZero N] (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ), B * A⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔ ∃ u : (ZMod N)ˣ, (u : ZMod N) * (A 1 0 : ZMod N) = (B 1 0 : ZMod N) ∧ (u : ZMod N) * (A 1 1 : ZMod N) = (B 1 1 : ZMod N)
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
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1.gamma0_bottom_row_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N≠0 and A,B∈SL₂(ℤ), and reduce all entries modulo N into R=ℤ/Nℤ. Membership of an integral determinant-one matrix in Γ₀(N) means that its reduced bottom-left entry is zero.
2. Suppose C=BA⁻¹ lies in Γ₀(N). Write its reduction as [[k,l],[0,e]]. Reducing det C=1 gives ke=1. Commutativity also gives ek=1, so e is the value of a unit u of R whose inverse has value k.
3. The group identity CA=B implies that the reduced bottom row of B is the bottom row of [[k,l],[0,e]]A. Matrix multiplication gives B₂₁=eA₂₁ and B₂₂=eA₂₂ in R. Thus u is the required simultaneous scaling unit, proving the forward implication.
4. Conversely, suppose a unit u satisfies the two displayed scaling equations. Write A=[[a,b],[c,d]] over ℤ, and write r,s for the reduced bottom entries of B. The determinant-one equation ad−bc=1 gives A⁻¹=[[d,−b],[−c,a]]. Consequently the reduced bottom-left entry of BA⁻¹ is r d−s c, with c,d now denoting their reductions. Substituting r=uc and s=ud gives ucd−udc=0 by commutativity. Hence BA⁻¹ lies in Γ₀(N), proving the reverse implication.
5. Both directions hold in every residue ring, including the zero ring R=ℤ/1ℤ, since the proof only used ring identities and explicit inverse equations for units.

## Key steps

1. Reduce C=BA⁻¹ in Gamma0 to an upper-triangular determinant-one matrix.
2. Use its diagonal entries to construct the bottom-right scaling unit.
3. Apply CA=B to obtain the two bottom-row scaling equations.
4. Conversely compute the bottom-left entry of BA⁻¹ and cancel it using the scaling equations.

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
