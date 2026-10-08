<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.elliptic_fixed_points-a1 -->

## Theorem `Submission.p10_17ae7b7d_cc_elliptic_fixed_points`

For every nonzero natural number N, let Γ₀(N) be the subgroup of SL₂(ℤ) whose bottom-left entry is zero modulo N, and let Q=SL₂(ℤ)/Γ₀(N) with left multiplication. Put S=((0,−1),(1,0)) and T=((1,1),(0,1)). The number of q∈Q fixed by S is #{x∈ℤ/Nℤ:x²+1=0}=ModularCurve.nuTwo N, and the number fixed by ST is #{x∈ℤ/Nℤ:x²+x+1=0}=ModularCurve.nuThree N.

Node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/372

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/417

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/441, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/442

## Lean problem

Declaration: `Submission.p10_17ae7b7d_cc_elliptic_fixed_points`

```lean
∀ (N : ℕ) [NeZero N], let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N; Nat.card {q : Q // ModularGroup.S • q = q} = ModularCurve.nuTwo N ∧ Nat.card {q : Q // (ModularGroup.S * ModularGroup.T) • q = q} = ModularCurve.nuThree N
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

- Parent DAG node: `root.gamma0_coset_counts-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N≠0. For N=1 the subgroup Γ₀(1) is all of SL₂(ℤ); the coset space and both polynomial root sets are singletons. Assume N>1. Put R=ℤ/Nℤ, H=Γ₀(N), and let P_N consist of rows (r,s) satisfying xr+ys=1 for some x,y∈R, modulo common unit scaling. This is an equivalence relation since units contain 1 and are closed under inverse and product. The set P_N is finite as a quotient of a subset of R².
2. The bottom row modulo N defines a bijection from right cosets Hα to P_N. Indeed, for α=((a,b),(c,d)), the determinant identity gives (−b)c+ad=1. A matrix η∈H has bottom row (0,e) modulo N, with e a unit by its determinant, so left multiplication by η scales bottom rows by e. Conversely, for rows (r′,s′)=u(r,s), the bottom-left entry of βα⁻¹ is r′s−s′r=0 modulo N, proving Hβ=Hα. Finally, p10_17ae7b7d_cc_lift_unimodular_row applies to every unimodular row at this nonzero N and supplies a representative matrix, proving surjectivity.
3. Right multiplication Hα↦HαB is well-defined and invertible, with inverse right multiplication by B⁻¹. Under the row bijection it is ordinary row multiplication by the reduction of B. Inversion Hα↦α⁻¹H bijects right cosets with Q and sends right multiplication by B to left multiplication by B⁻¹. The fixed sets of left multiplication by B and B⁻¹ coincide: either fixed-point equation implies the other by applying the inverse map. We may therefore count right-multiplication fixed points for S and U=ST.
4. Matrix multiplication gives (r,s)S=(s,−r) and (r,s)U=(s,s−r). An S-fixed class consequently has a unit u with s=ur and −r=us. If xr+ys=1, the first equation yields (x+yu)r=1. Thus r is a unit, and the class has a representative [1:t], where t=r⁻¹s. This representative is unique: a unit carrying (1,t) to (1,t′) must be 1.
5. For [1:t], the S-fixed equations are t=u and −1=ut, hence t²+1=0. Conversely, if t²+1=0 then t(−t)=1, so t is a unit and (t,−1)=t(1,t). The row (1,t) is unimodular, and its class is S-fixed. This gives a bijection between the S-fixed classes and the roots of t²+1=0 in R.
6. A U-fixed class has a unit u with s=ur and s−r=us. Using a unimodularity witness again gives (x+yu)r=1, so there is a unique representative [1:t]. The normalized equations are t=u and t−1=ut, equivalently t²−t+1=0.
7. Conversely, t²−t+1=0 implies t(1−t)=1, so t is a unit; also (t,t−1)=t(1,t). Thus [1:t] is U-fixed. The same uniqueness of normalized representatives gives a bijection from U-fixed classes to the roots of t²−t+1=0.
8. Negation t↦−t is an involution of R and takes t²−t+1=0 exactly to x²+x+1=0. Hence it bijects these root sets. Transfer the two fixed-point bijections to Q using step 3. By the definitions of nuTwo and nuThree as the natural cardinalities of these root subtypes, the two asserted equalities follow.

## Key steps

1. Establish the right-coset row-class bijection using row lifting.
2. Transfer left-action fixed points to right multiplication by inversion.
3. Show the first coordinate of every S- or ST-fixed unimodular row is a unit.
4. Normalize S-fixed rows to obtain the roots of t²+1.
5. Normalize ST-fixed rows to obtain the roots of t²−t+1.
6. Negate the parameter to obtain the roots defining nuThree.

## Reference use

### local-project

Queries:
- `surject|lift|coprime|Coprime`
- `SpecialLinearGroup.*surject|surject.*SpecialLinearGroup|[Gg]amma0.*card|[Gg]amma0.*index|[Pp]rojectiveLine.*[Cc]ard|[Cc]ard.*[Pp]rojectiveLine|[Tt]ransvection.*surject`
- `p10_17ae7b7d_cc_(lift_unimodular_row|index|elliptic_fixed_points|translation_orbits)`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o TargetAbsence.olean TargetAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o ChildTypes.olean ChildTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ProjectiveLineMatrixAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Totient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p10-coset-split-nairohng/TargetAbsence.lean`
- `/tmp/p10-coset-split-nairohng/ChildTypes.lean`
- `/tmp/p10-coset-split-nairohng/ChildTypes.log`
- `/tmp/p10-coset-split-nairohng/report.json`

The snapshot matches project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; both tracked snapshot trees and all nine pinned dependency checkouts were clean. Existing infrastructure supplies same-ring Bézout row completion, Chinese remaindering, totient formulas, Gamma0 finiteness, and quotient actions. Searches found no matching integer lift of a unimodular residue row or the requested counting formulas, and no reservation of the proposed names in local DAGs. The separate projective-line modules are not in the frozen imports. All four literal types compiled after import Submission in /tmp/p10-coset-split-nairohng; reflexivity probes checked left coset multiplication, subgroup restriction and matrix multiplication. The types and selected imported lemmas reported only propext, Classical.choice and Quot.sound. Policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 matched; only listed lines 10–12 were omitted in the disposable copy, and Lean verified all 56 targets absent. The report records exact omitted lines, reversible reconstruction, original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and build hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539. Original contract and Submission were unchanged. These are interface diagnostics, not comparator acceptance of proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
