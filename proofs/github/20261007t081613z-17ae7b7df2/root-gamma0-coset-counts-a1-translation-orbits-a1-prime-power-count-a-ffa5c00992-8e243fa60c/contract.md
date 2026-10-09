<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.translation_charts-a1 -->

## Theorem `Submission.p10_17ae7b7d_pp_translation_charts`

Let p be prime and a ≥ 1, put M = p^a, R = Z/MZ, H = Γ₀(M), Q = SL₂(Z)/H, and B = {z ∈ R : p divides z.val}, where z.val is the representative in [0,M). Let T = ((1,1),(0,1)), acting on Q by left multiplication. There exists a bijection e : Q ≃ R ⊔ B such that, for every t ∈ R, e(T⁻¹ · e⁻¹(inl t)) = inl(t+1), and for every z ∈ B there exists w ∈ B with e(T⁻¹ · e⁻¹(inr z)) = inr w and w = z(1+z)⁻¹. The inverse is the ZMod inverse, which agrees with unit inversion whenever its argument is a unit.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.translation_charts-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/452

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/441, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/546

## Lean problem

Declaration: `Submission.p10_17ae7b7d_pp_translation_charts`

```lean
∀ (p a : ℕ), Nat.Prime p → 1 ≤ a → let R := ZMod (p ^ a); let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (p ^ a); ∃ e : Q ≃ (R ⊕ {z : R // p ∣ z.val}), (∀ t : R, e (ModularGroup.T⁻¹ • e.symm (Sum.inl t)) = Sum.inl (t + 1)) ∧ (∀ z : {z : R // p ∣ z.val}, ∃ w : {z : R // p ∣ z.val}, e (ModularGroup.T⁻¹ • e.symm (Sum.inr z)) = Sum.inr w ∧ w.1 = z.1 * (1 + z.1)⁻¹)
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

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.translation_charts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Set M = p^a. Since p is prime and a ≥ 1, M > 1 and p divides M. An element x of R is a unit exactly when p does not divide x.val: if p does not divide this representative, it is coprime to M and a Bezout identity supplies an inverse; if p divides it, reduction modulo p sends x to zero and precludes an inverse. Reduction modulo p sends x to zero exactly when p divides x.val.
2. Write a determinant-one integer matrix α as ((A,B),(C,D)). Its bottom row (r,s) modulo M is unimodular, since (-B)r + As = 1. At least one of r,s is a unit: otherwise their reductions modulo p are both zero, contradicting this identity. Common multiplication by a unit preserves unimodularity, with the witnesses multiplied by the inverse unit.
3. Every such row has a unique normalized form of one of two kinds. If r is a unit, scale by r⁻¹ to obtain (1,t), with t = r⁻¹s. Otherwise s is a unit, and scaling by s⁻¹ gives (z,1), with z = s⁻¹r and p dividing z.val. The two kinds cannot be related by a unit scaling, since their first coordinates are respectively a unit and a nonunit. Two normalized rows of the same kind related by a unit scaling have scaling factor 1, by comparing their coordinate equal to 1, so their parameters agree. Unit scaling preserves the kind and these normalized parameters.
4. For matrices α,β, the cosets α⁻¹H and β⁻¹H agree exactly when their bottom rows modulo M are related by a unit scaling. Indeed, equality of the cosets gives η = βα⁻¹ ∈ H and β = ηα. Modulo M the bottom-left entry of η is zero, and det η = 1 gives η₁₁η₂₂ = 1. Thus η₂₂ is a unit and the bottom row of β is η₂₂ times that of α. Conversely, if the rows are (r,s) and (r′,s′) = u(r,s), then the bottom-left entry of βα⁻¹ modulo M is r′s - s′r = 0. Hence βα⁻¹ ∈ H and the cosets agree.
5. Define e on the coset α⁻¹H by the normalized bottom row of α, recording (1,t) as inl t and (z,1) as inr z. Steps 3 and 4 make this well defined and injective. For surjectivity, choose integer representatives t̃ and z̃. The determinant-one matrices ((0,-1),(1,t̃)) and ((1,0),(z̃,1)) have the required normalized bottom rows. Their inverse cosets map respectively to inl t and inr z. Therefore e is a bijection, and thus an equivalence with inverse e⁻¹.
6. Left multiplication by T⁻¹ sends α⁻¹H to (αT)⁻¹H. Right multiplication of α by T sends its bottom row (r,s) to (r,r+s). This operation respects common unit scaling, so its effect may be computed using the normalized rows. On (1,t) it gives (1,t+1). Applying the definition of e proves the first required identity for every t.
7. On (z,1), with z ∈ B, the new row is (z,1+z). Its second coordinate reduces to 1 modulo p and is therefore a unit by step 1. Normalization gives (w,1), where w = z(1+z)⁻¹; the ZMod inverse here is the inverse of that unit. Reducing w modulo p gives zero, so p divides w.val and w ∈ B. This w satisfies both assertions required in the second identity, completing the proof.

## Key steps

1. Characterize units modulo p^a by nondivisibility by p.
2. Normalize unimodular rows uniquely into disjoint forms (1,t) and (z,1) with p dividing z.val.
3. Identify equality of inverse cosets with common unit scaling of bottom rows.
4. Construct the bijection and prove surjectivity using explicit determinant-one matrices.
5. Compute T⁻¹ on inverse cosets by right multiplication by T, obtaining t ↦ t+1 and z ↦ z(1+z)⁻¹.

## Reference use

### local-project

Queries:
- `unimodular|ProjectiveLine|cusp|orbit|zpow`
- `isUnit_iff_coprime|val_lt|mul_inv_of_unit|inv_mul_of_unit|isUnit.*pow|isUnit.*iff|natCast.*val|natCast_eq_zero|val_natCast`
- `totient_prime_pow|totient_one|card|orbitRel|mem_Gamma0|def Gamma0|eq_iff`
- `prime_power.*(orbit|chart)|valuation.*strat|translation.*chart|fractional.*(iterat|period)`
- `p10_17ae7b7d_pp_translation_charts|p10_17ae7b7d_pp_fractional_iterates|p10_17ae7b7d_pp_stratum_card`
- `python3 .humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/prime-power-split-ipfffwyj/run.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Totient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/prime-power-split-ipfffwyj/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/prime-power-split-ipfffwyj/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/prime-power-split-ipfffwyj/report.json`

The snapshots match project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; both snapshots and all nine pinned dependency checkouts are clean. Relevant infrastructure includes ZMod.isUnit_natCast_iff_not_dvd_pow, ZMod.inv_coe_unit, ZMod.mul_inv_of_unit, Nat.totient_prime_pow, the Gamma0 membership definition, and coset-action/orbit equivalences. No matching chart, fractional-period, or valuation-stratum theorem was found. The separate projective-line module supplies useful definitions but is absent under the frozen imports; the proposed types avoid those unavailable declarations. All three exact types elaborate after import Submission from proof-base c77074cc2682d4bf219f2909b6b4767445f7f7bc in the disposable compiler copy. Reflexivity probes verify left coset multiplication, function iteration, and matrix multiplication. Proposed names have no collisions in the DAG, node records, Submission, or imported environment. Audited interfaces and library lemmas depend only on propext, Classical.choice, and Quot.sound. Header-policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 matched; only listed lines 10–12 were omitted, and Lean verified all 56 targets absent. The report records exact omissions, reversible reconstruction, and original/build hashes. The original contract and working tree remain unchanged. These are interface diagnostics, not comparator acceptance of theorem proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/738

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
