<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1 -->

## Theorem `Submission.p10_17ae7b7d_idx_prime_power_row_card`

Let p be a prime natural number and a a positive natural number. Put R=ℤ/pᵃℤ. Let U={(r,s)∈R² | ∃x,y∈R, xr+ys=1}, and let P be its quotient by simultaneous multiplication of both coordinates by a unit of R. Then Nat.card P=pᵃ+p^(a−1).

Node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/418

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/485, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/486

## Lean problem

Declaration: `Submission.p10_17ae7b7d_idx_prime_power_row_card`

```lean
∀ (p a : ℕ), p.Prime → 0 < a → Nat.card (Quot (fun v w : {v : ZMod (p ^ a) × ZMod (p ^ a) // ∃ x y : ZMod (p ^ a), x * v.1 + y * v.2 = 1} => ∃ u : (ZMod (p ^ a))ˣ, (u : ZMod (p ^ a)) * v.1.1 = w.1.1 ∧ (u : ZMod (p ^ a)) * v.1.2 = w.1.2)) = p ^ a + p ^ (a - 1)
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

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix p prime and a>0. Set q=pᵃ and R=ℤ/qℤ. Since p≥2, q>0 and q=p·p^(a−1). Unit scaling preserves a witness xr+ys=1 by replacing x,y with xu⁻¹,yu⁻¹. The identity, inverse, and product of units make scaling an equivalence relation. Thus the displayed Quot identifies exactly the unit-scaled rows. It is finite because it is a quotient of a subset of the finite set R².
2. A residue r is a unit exactly when its integer representative k is not divisible by p. If r has an inverse, reducing the inverse equation modulo p shows that k cannot be zero modulo p. Conversely, if p does not divide k, then k is coprime to pᵃ: any prime divisor of a common divisor would divide pᵃ and hence equal p, a contradiction. A Bézout identity xk+ypᵃ=1 reduces to an inverse for r. Divisibility of k by p is independent of the representative because p divides q.
3. A row (r,s) is unimodular exactly when at least one coordinate is a unit. A unit coordinate supplies a linear-combination witness using its inverse and coefficient zero for the other coordinate. If neither coordinate is a unit, step 2 says both reduce to zero modulo p. Reducing any proposed equation xr+ys=1 modulo p would then give 0=1 in ℤ/pℤ, impossible because p≥2.
4. If r is a unit, scaling (r,s) by r⁻¹ gives the representative (1,t), where t=r⁻¹s is arbitrary in R. If r is not a unit, step 3 makes s a unit; scaling by s⁻¹ gives (z,1). Here z=s⁻¹r is still a nonunit, since otherwise r=sz would be a unit. By step 2, z is precisely a residue divisible by p. Conversely every row (1,t) and every row (z,1) of this second kind is unimodular.
5. These representatives are unique and the two families are disjoint. A scaling unit taking (1,t) to (1,t′) must equal 1 by the first coordinate, hence t=t′. A scaling unit taking (z,1) to (z′,1) must equal 1 by the second coordinate, hence z=z′. A scaling unit taking (1,t) to (z,1) would equal z, contradicting the fact that z is a nonunit. Since scaling is already an equivalence relation, these statements apply to equality of quotient classes.
6. The first family has |R|=q=pᵃ members. The second family has p^(a−1) members: the representatives between 0 and q−1 divisible by p are exactly pk with 0≤k<p^(a−1). All such pk lie in that interval, distinct k give distinct representatives, and every multiple of p in the interval has this form. The disjoint classification in steps 4–5 therefore gives Nat.card P=pᵃ+p^(a−1).

## Key steps

1. Identify quotient equality with unit scaling and establish finiteness.
2. Characterize units modulo pᵃ by nondivisibility by p.
3. Characterize unimodular rows by the existence of a unit coordinate.
4. Normalize uniquely into the disjoint charts (1,t) and (z,1), with p dividing z.
5. Count the charts as pᵃ and p^(a−1).

## Reference use

### local-project

Queries:
- `dedekindPsi|ProjectiveLine|unimodularRow|Gamma0`
- `card.*ProjectiveLine|ProjectiveLine.*card|Gamma0.*(index|card)|(index|card).*Gamma0|dedekindPsi`
- `chineseRemainder|primeFactors|factorization|isUnit_iff|isUnit.*coprime`
- `prod_pow_primeFactors|prod.*factorization|factorization.*prod|squarefree_iff|Squarefree.*factorization`
- `rg -n 'p10_17ae7b7d_idx_(coset_row_card|prime_power_row_card|crt_row_card|dedekind_psi_product)' .humanize --glob 'dag.json' --glob 'parent-child-handoff.json'`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o TargetAbsence.olean TargetAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o ChildTypes.olean ChildTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-coset-index-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Factorization/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Squarefree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/index-split-ssqaob6l/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/index-split-ssqaob6l/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/index-split-ssqaob6l/report.json`

The snapshot matches project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Both tracked snapshot trees and all nine pinned dependency checkouts were clean. The sources supply the squarefree-divisor definition of dedekindPsi, Chinese remaindering, the prime-power unit criterion, prime factorization, and the left-coset convention. No matching coset-index or projective-row cardinality theorem was found. The projective-line module is outside the frozen imports, so the proposed types express its mathematical quotient explicitly using Quot. No proposed name occurred in local DAGs or frozen handoffs. All four exact types compiled after import Submission; reflexivity checks confirmed the left-coset quotient, scalar unit multiplication, and special-linear matrix multiplication. The types and checked library declarations have only propext, Classical.choice and Quot.sound as transitive axioms. The matching policy digest was 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96. Only listed lines 10–12 were omitted in the disposable compiler copy; Lean confirmed all 56 targets absent. The receipt records exact omitted text, reversible reconstruction, original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and build hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539. Original contracts and handoffs were unchanged. These are interface diagnostics, not comparator acceptance of theorem proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
