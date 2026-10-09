<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1 -->

## Theorem `Submission.p10_17ae7b7d_to_coprime_count_mul`

Let m and n be nonzero natural numbers with gcd(m,n) = 1. For each positive k, let Γ₀(k) be the subgroup of SL₂(ℤ) whose bottom-left entry is divisible by k, and let C(k) be the number of orbits of {Tᶻ : z ∈ ℤ}, where T = ((1,1),(0,1)), acting by left multiplication on SL₂(ℤ)/Γ₀(k). Then C(mn) = C(m)C(n).

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/420

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/520, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/521, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/522

## Lean problem

Declaration: `Submission.p10_17ae7b7d_to_coprime_count_mul`

```lean
∀ (m n : ℕ) [NeZero m] [NeZero n], Nat.Coprime m n → Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (m * n)))) = Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 m))) * Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 n)))
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
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix nonzero coprime m,n. Write C(k) for the orbit count in the statement. Since every integer is zero modulo 1, Γ₀(1) = SL₂(ℤ); its coset space and orbit space are singletons, so C(1) = 1. If m = 1 or n = 1, the claimed identity follows immediately. Assume henceforth m,n > 1.
2. We use the elementary Chinese remainder construction. For coprime positive A,B, choose integers u,v with uA + vB = 1. Given residues x modulo A and y modulo B, the integer xvB + yuA realizes both residues. If a difference is divisible by A and B, write it as At. The same Bézout identity shows B divides t, so AB divides the difference. This proves the bijection ℤ/ABℤ ≃ ℤ/Aℤ × ℤ/Bℤ. Reduction preserves addition and multiplication, making it a ring isomorphism. Iteration gives the corresponding assertion for finitely many pairwise coprime moduli.
3. For any K > 1, put R_K = ℤ/Kℤ and let P_K be the quotient of unimodular rows (r,s) by common unit scaling. Here unimodularity means xr + ys = 1 for some x,y ∈ R_K. Scaling preserves this condition using inverse-scaled witnesses, and the unit laws prove the equivalence relation. The set P_K is finite because R_K² is finite. Every unimodular row has a primitive integer lift, as follows. Choose a positive integer c representing r, using c = K when the least nonnegative representative is zero, and choose an integer s₀ representing s. For every prime q dividing c but not K, require d ≡ 1 modulo q, and also require d ≡ s₀ modulo K. These moduli are pairwise coprime, so step 2 supplies d. If a prime q divided both c and d, then either q does not divide K, contradicting d ≡ 1 modulo q, or q divides K. In the latter case, reducing a unimodularity identity modulo q contradicts both coordinates being zero. Thus gcd(c,d) = 1. Bézout supplies integers a,b with ad−bc = 1, and ((a,b),(c,d)) is a determinant-one integer matrix with the prescribed bottom row modulo K.
4. Let H_K = Γ₀(K). The bottom row gives a bijection from right cosets H_Kα to P_K. A determinant-one matrix has unimodular bottom row. Left multiplication by η ∈ H_K scales that row by the lower-right entry of η, which is a unit because the determinant is 1 and the lower-left entry vanishes modulo K. Conversely, if the rows of β and α satisfy (r′,s′) = u(r,s), then the lower-left entry of βα⁻¹ is r′s−s′r = 0 modulo K, so H_Kβ = H_Kα. Surjectivity follows from the primitive lift in step 3.
5. Define τ_K[r:s] = [r:r+s]. It respects scaling, preserves unimodularity by the identity (x−y)r+y(r+s) = xr+ys, and has inverse [r:s] ↦ [r:s−r]. It corresponds to right multiplication by T on right cosets. Inversion H_Kα ↦ α⁻¹H_K intertwines that operation with left multiplication by T⁻¹ on SL₂(ℤ)/H_K. Since T and T⁻¹ generate the same subgroup, C(K) is the number of cycles of τ_K.
6. Apply step 2 to m,n. Under R_{mn} ≃ R_m × R_n, unimodularity is componentwise: witnesses project, and witnesses in the two factors assemble through the ring isomorphism. Units are also componentwise, because inverses project and assemble. Thus reduction induces a bijection P_{mn} ≃ P_m × P_n. Surjectivity follows by assembling representatives and their unimodularity witnesses. For injectivity, units witnessing equivalence in the two components assemble to one unit witnessing equivalence modulo mn. Addition is componentwise, so this bijection takes τ_{mn} to the componentwise permutation (τ_m,τ_n).
7. For every positive K and every row class, τ_K^K[r:s] = [r:s+Kr] = [r:s]. Thus every cycle has a positive length ℓ dividing K. Indeed, choose its least positive return time ℓ, which exists because K is a return time; division K = qℓ+r with 0 ≤ r < ℓ makes r a return time, so minimality forces r = 0. In particular, any cycle length ℓ_m of τ_m and any cycle length ℓ_n of τ_n are coprime, because they divide the coprime numbers m,n.
8. Choose a cycle A of τ_m and a cycle B of τ_n, with basepoints x,y and lengths ℓ_m,ℓ_n. Every point of A × B has the form (τ_m^i x,τ_n^j y). By step 2 there is a nonnegative integer t congruent to i modulo ℓ_m and to j modulo ℓ_n. The t-th componentwise iterate of (x,y) is that point. Therefore A × B is one cycle. Conversely, componentwise iteration cannot change either component's cycle, so every product cycle lies in exactly one such A × B. The products A × B partition P_m × P_n, proving that its cycle count is the product of the two cycle counts.
9. Combining the equivariant bijection of step 6, the count in step 8, and the identifications of step 5 gives C(mn) = C(m)C(n), which is the required equality of Nat.card values.

## Key steps

1. Handle level 1 and establish the elementary CRT bijection.
2. Lift unimodular residue rows to primitive integer rows using CRT and Bézout.
3. Identify cosets with finite row classes and translation with a row permutation.
4. Use CRT to identify the level-mn row permutation with the product permutation.
5. Show every local cycle length divides its level.
6. Use coprimality and CRT on iteration numbers to make each product of cycles one cycle.
7. Count the resulting partition into product cycles.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/726

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
