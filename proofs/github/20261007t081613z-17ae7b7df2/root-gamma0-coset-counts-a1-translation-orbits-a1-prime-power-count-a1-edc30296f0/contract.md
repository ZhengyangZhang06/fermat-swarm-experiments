<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1 -->

## Theorem `Submission.p10_17ae7b7d_to_prime_power_count`

Let p be a prime natural number and let a be a natural number with 1 ≤ a. Let Γ₀(pᵃ) consist of the matrices in SL₂(ℤ) whose bottom-left entry is divisible by pᵃ. On Q = SL₂(ℤ)/Γ₀(pᵃ), use left multiplication and put T = ((1,1),(0,1)). The number of orbits of the subgroup {Tⁿ : n ∈ ℤ} on Q is the sum, for 0 ≤ j ≤ a, of φ(p^{min(j,a−j)}), where φ is Euler's totient.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/420

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/482, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/483, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/484

## Lean problem

Declaration: `Submission.p10_17ae7b7d_to_prime_power_count`

```lean
∀ (p a : ℕ), Nat.Prime p → 1 ≤ a → Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (p ^ a)))) = (Finset.range (a + 1)).sum (fun j => Nat.totient (p ^ min j (a - j)))
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

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a prime p and a ≥ 1, and put M = pᵃ, R = ℤ/Mℤ and H = Γ₀(M). Then M > 1. A residue is a unit precisely when its integer representative is not divisible by p: in that case its representative is coprime to pᵃ, so a Bézout identity gives an inverse modulo M; if it is divisible by p, reduction modulo p rules out an inverse.
2. Let P be the set of unimodular rows (r,s) over R modulo common unit scaling. Unimodular means xr + ys = 1 for some x,y ∈ R. Multiplication of both coordinates by a unit preserves this property by multiplying the witnesses by its inverse. Identity, inverse and multiplication of units prove that scaling is an equivalence relation. Thus P is a finite quotient of a subset of R². At least one coordinate of a unimodular row is a unit, since otherwise reduction modulo p would make every linear combination zero. If r is a unit, normalize to [1:t]. Otherwise s is a unit, and normalization gives [z:1] with p dividing z. These charts are disjoint because their first coordinates are respectively units and nonunits. Within either chart, the coordinate equal to 1 forces the scaling unit to be 1, proving uniqueness of its parameter.
3. The bottom row modulo M identifies right cosets Hα with P. For α = ((A,B),(C,D)), the determinant identity gives (−B)C + AD = 1, so its bottom row is unimodular. If η ∈ H, its lower-left entry is zero modulo M and its determinant shows its lower-right entry is a unit. Hence left multiplication by η scales the bottom row by that unit. Conversely, if the bottom rows of β and α are (r′,s′) = u(r,s), then the bottom-left entry of βα⁻¹ is r′s − s′r = 0 modulo M. Therefore βα⁻¹ ∈ H and Hβ = Hα. Surjectivity follows directly from the charts: choosing integer representatives t and z, the determinant-one matrices ((0,−1),(1,t)) and ((1,0),(z,1)) realize [1:t] and [z:1]. This proves the asserted bijection without an additional lifting hypothesis.
4. Right multiplication by T induces τ[r:s] = [r:r+s]. Scaling compatibility is immediate, and unimodularity is preserved because (x−y)r + y(r+s) = 1 whenever xr + ys = 1. The inverse is [r:s] ↦ [r:s−r], so τ is a permutation. Inversion Hα ↦ α⁻¹H identifies this permutation with left multiplication by T⁻¹ on Q. The subgroups generated by T and T⁻¹ coincide. Consequently the required orbit count is the number of cycles of τ, including singleton cycles.
5. On the first chart, τ[1:t] = [1:t+1]. The M residues t form exactly one cycle: integer translation reaches every residue, and a nonnegative iteration number n returns to t exactly when M divides n. This contributes one cycle of length pᵃ.
6. On the second chart, p divides z, so 1+nz is a unit for every nonnegative integer n. Iterating addition in the unnormalized row gives τⁿ[z:1] = [z:1+nz] = [z/(1+nz):1], where division means multiplication by the unit inverse. These points remain in the second chart. By uniqueness of its normalized parameter, return to [z:1] occurs exactly when z/(1+nz) = z. Multiplication by 1+nz shows this is equivalent to nz² = 0 in R. Multiplication by a unit preserves divisibility by every p-power, in both directions, so each exact-valuation stratum is invariant.
7. The parameter z = 0 is fixed. Every other parameter divisible by p has a unique exact valuation j with 1 ≤ j < a: its representative between 1 and M−1 is pʲv with p not dividing v. Such v is a unit modulo M. The return condition becomes pᵃ dividing np^{2j}v², equivalently pᵃ dividing np^{2j}. If 2j < a this is equivalent to p^{a−2j} dividing n; if 2j ≥ a it holds for every n. Thus the least positive return time throughout this stratum is L_j = p^{max(a−2j,0)}.
8. Multiples of pʲ modulo pᵃ are uniquely pʲt with 0 ≤ t < p^{a−j}, so there are p^{a−j} of them. Removing the p^{a−j−1} multiples of p^{j+1} leaves p^{a−j}−p^{a−j−1} parameters of exact valuation j. Every cycle in this invariant stratum has L_j elements: the first L_j iterates are distinct by minimality of the return time, and all later iterates reduce to them by division with remainder. Therefore the stratum contains (p^{a−j}−p^{a−j−1})/L_j cycles. If 2j < a this equals pʲ−p^{j−1}; if 2j ≥ a it equals p^{a−j}−p^{a−j−1}.
9. For every b ≥ 1, the residues coprime to pᵇ are precisely the residues not divisible by p. Counting them gives φ(pᵇ) = pᵇ−p^{b−1}. Hence the contribution in step 8 is φ(p^{min(j,a−j)}). The first-chart cycle supplies the j = 0 term φ(1) = 1, and z = 0 supplies the j = a term φ(1) = 1. The charts and valuation strata partition P, so summing gives exactly the stated sum over 0 ≤ j ≤ a. Step 4 transfers this count to the orbit quotient in the conclusion.

## Key steps

1. Classify unimodular residue rows into the two unique prime-power charts.
2. Identify right cosets with row classes using explicit determinant-one chart representatives.
3. Transfer left translation orbits to cycles of [r:s] ↦ [r:r+s].
4. Compute the first-chart cycle and the second-chart return condition nz² = 0.
5. Determine exact-valuation periods and stratum cardinalities.
6. Divide by the common periods and identify the totient terms, including both endpoints.

## Reference use

### local-project

Queries:
- `cuspCount|genusFormula`
- `totient_mul|totient_prime_pow|chineseRemainder|prime_pow|isUnit_iff_coprime`
- `cuspCount.*(mul|prod|pow)|translation_orbits|orbit.*Gamma0|Gamma0.*orbit`
- `multiplicative_factorization|prod_pow_factorization|divisors.*prod|divisors_prime_pow`
- `def orbitRel|orbitRel_apply|orbitRel_iff|instance.*Quotient|smul_mk`
- `p10_17ae7b7d_to_(prime_power_count|coprime_count_mul|cusp_count_factorization)`
- `python3 /tmp/p10-translation-split-nhp6svxx/run.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-translation-orbits-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Totient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Factorization/Divisors.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Factorization/Induction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p10-translation-split-nhp6svxx/TargetAbsence.lean`
- `/tmp/p10-translation-split-nhp6svxx/ChildTypes.lean`
- `/tmp/p10-translation-split-nhp6svxx/ChildTypes.log`
- `/tmp/p10-translation-split-nhp6svxx/statements.json`
- `/tmp/p10-translation-split-nhp6svxx/report.json`

The clean reference snapshots match project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine dependency checkouts matched their pins and had clean tracked files. Relevant infrastructure includes ZMod.chineseRemainder, the prime-power unit criterion, totient formulas, divisor parametrization by factorization, and left coset actions. No matching orbit-count or cuspCount product formula was found. The separate projective-line module is outside the frozen imports, so no child type references its declarations. All three exact child types elaborated after import Submission in the disposable compiler context. Reflexivity probes verified left coset multiplication, subgroup restriction, and matrix multiplication. Proposed names had no matches in the local records or imported environment. Interface definitions and audited library declarations use only propext, Classical.choice, and Quot.sound. The matching header-policy digest was 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; only lines 10–12 were omitted, and Lean verified all 56 targets absent. The report records exact omissions, reversible reconstruction, original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and build hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539. The frozen contract and original Submission header remain unchanged. These checks establish interface compatibility, not comparator acceptance of theorem proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
