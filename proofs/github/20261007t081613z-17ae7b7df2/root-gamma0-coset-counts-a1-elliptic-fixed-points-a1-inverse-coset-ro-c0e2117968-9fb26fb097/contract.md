<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.elliptic_fixed_points-a1.inverse_coset_row_criterion-a1 -->

## Theorem `Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff`

Let N be a nonzero natural number, R=ℤ/Nℤ, G=SL₂(ℤ), and H=Γ₀(N)={M∈G : M₁₀=0 in R}. For any A,B∈G, the left cosets A⁻¹H and B⁻¹H are equal if and only if there exists a unit u∈Rˣ such that B₁₀=uA₁₀ and B₁₁=uA₁₁ in R.

Node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1.inverse_coset_row_criterion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/419

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff`

```lean
∀ (N : ℕ) [NeZero N] (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ), (QuotientGroup.mk (A⁻¹) : (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = QuotientGroup.mk (B⁻¹) ↔ ∃ u : (ZMod N)ˣ, (B 1 0 : ZMod N) = (u : ZMod N) * (A 1 0 : ZMod N) ∧ (B 1 1 : ZMod N) = (u : ZMod N) * (A 1 1 : ZMod N)
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

- Parent DAG node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1.inverse_coset_row_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N≠0 and A,B∈SL₂(ℤ). Work in the commutative ring R=ℤ/Nℤ when discussing matrix entries. Write the bottom rows of A and B as (c,d) and (c′,d′), respectively, and put H=Γ₀(N).
2. For any subgroup H, equality gH=hH is equivalent to g⁻¹h∈H: membership expresses h as gh₀ for h₀∈H, and conversely equal cosets imply h∈gH. Applying this to g=A⁻¹ and h=B⁻¹ shows that A⁻¹H=B⁻¹H is equivalent to AB⁻¹∈H. Since a subgroup is closed under inversion, this is also equivalent to E=BA⁻¹ belonging to H.
3. Suppose the cosets are equal. By step 2, E∈H, so its reduced matrix has the form ((a,b),(0,e)). Reduction preserves the determinant, and det E=1, hence ae=1 in R. Commutativity also gives ea=1. Thus e is the value of a unit u with inverse a.
4. The identity B=EA follows from E=BA⁻¹. Multiplying the bottom row (0,e) of E by A gives c′=ec and d′=ed. The unit u from step 3 therefore satisfies both required scaling equations.
5. Conversely, suppose there is a unit u with c′=uc and d′=ud. Since det A=1, if A=((a,b),(c,d)), then A⁻¹=((d,−b),(−c,a)). Consequently the reduced bottom-left entry of E=BA⁻¹ is c′d−d′c. Substituting the scaling equations gives ucd−udc=0 by commutativity. Hence E∈Γ₀(N).
6. Step 2 now gives A⁻¹H=B⁻¹H. This proves both implications. Every calculation remains valid in ℤ/1ℤ, so no additional restriction on N is needed.

## Key steps

1. Translate equality of inverse left cosets into BA⁻¹∈Γ₀(N).
2. Use determinant one to show the bottom-right entry of an upper-triangular reduction is a unit.
3. Multiply B=(BA⁻¹)A to obtain common unit scaling of bottom rows.
4. Conversely compute (BA⁻¹)₁₀=c′d−d′c and use scaling to make it zero.
5. Recover the required coset equality from subgroup membership.

## Reference use

### local-project

Queries:
- `nuTwo|nuThree|unimodularRow|ProjectiveLine|fixedPoints`
- `def Gamma0|mem_Gamma0|rightRel|quotientRightRelEquivQuotientLeftRel|eq_iff_div_mem|inv.*Quotient|Quotient.*inv`
- `isUnit_iff_exists|isUnit_iff.*mul|SL2_inv_expl|coe.*S|coe.*T`
- `nuTwo|nuThree|[Ff]ixed.*[Rr]oot|[Rr]oot.*[Ff]ixed|[Cc]oset.*[Uu]nimodular|[Uu]nimodular.*[Cc]oset`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. GenusNumerics defines nuTwo and nuThree as the stated root-subtype cardinalities. ProjectiveLine defines unimodular rows modulo common unit scaling. CongruenceSubgroups provides Gamma0_mem; Coset/Defs provides the left/right coset relations and their inversion equivalence; SpecialLinearGroup provides SL2_inv_expl and the concrete S and T matrices. No matching fixed-point-count theorem was found in the searched project Definitions and mathlib ModularForms files. The proposed interfaces use the imported coset and ring infrastructure directly.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/508

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
