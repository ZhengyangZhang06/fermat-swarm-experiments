<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1 -->

## Theorem `Submission.p10_17ae7b7d_cc_translation_orbits`

For every nonzero natural number N, let Γ₀(N) be the subgroup of SL₂(ℤ) whose bottom-left entry is zero modulo N, and let Q=SL₂(ℤ)/Γ₀(N) with left multiplication. Put T=((1,1),(0,1)). The number of orbits on Q of the subgroup {Tⁿ:n∈ℤ} is ∑_{d∣N}φ(gcd(d,N/d)), where φ is Euler’s totient; this is ModularCurve.cuspCount N.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/372

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/417

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/452, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/453, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/454

## Lean problem

Declaration: `Submission.p10_17ae7b7d_cc_translation_orbits`

```lean
∀ (N : ℕ) [NeZero N], let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N; Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) Q)) = ModularCurve.cuspCount N
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
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N≠0. If N=1, Γ₀(1)=SL₂(ℤ), the coset space and its orbit space are singletons, and the divisor sum is φ(gcd(1,1))=φ(1)=1. Assume N>1 and set R=ℤ/Nℤ and H=Γ₀(N).
2. Let P_N be the quotient of unimodular rows (r,s) over R by common unit scaling; unimodular means xr+ys=1 for some x,y∈R. The unit laws make this an equivalence relation and preserve unimodularity. This quotient is finite because R² is finite. The bottom row gives a bijection from right cosets Hα to P_N: determinants imply unimodularity; left multiplication by η∈H scales bottom rows by its bottom-right entry, which is a unit modulo N; and if (r′,s′)=u(r,s), the bottom-left entry of βα⁻¹ is r′s−s′r=0, giving Hβ=Hα. Surjectivity follows by applying p10_17ae7b7d_cc_lift_unimodular_row to each unimodular row.
3. Right multiplication by T induces τ[r:s]=[r:r+s] on P_N. This respects unit scaling and preserves unimodularity since (x−y)r+y(r+s)=xr+ys; its inverse is [r:s]↦[r:s−r]. Inversion Hα↦α⁻¹H intertwines it with left multiplication by T⁻¹ on Q. Therefore its cycles are in bijection with the requested orbits: the groups generated by T and T⁻¹ agree, and on a finite set integer powers of a permutation give precisely its cycles.
4. Factor N=∏ᵢpᵢ^{aᵢ} with distinct primes and aᵢ≥1. Existence follows by induction on positive integers, splitting composites; uniqueness follows from Euclid's lemma, which follows by multiplying a Bézout identity for p,a by b whenever p∤a and p∣ab. Chinese remaindering gives R≃∏ᵢℤ/pᵢ^{aᵢ}ℤ. For completeness, if ua+vb=1, Avb+Bua realizes residues A modulo a and B modulo b; a number divisible by both a and b is divisible by ab, since n=at and b∣at imply b∣t by this same identity. This proves the two-modulus bijection; induction proves the product assertion. Reduction respects ring operations.
5. Unimodularity and being a unit are componentwise under this ring isomorphism: witnesses of linear combinations and inverses project and assemble. Common unit scalings likewise project and assemble. Hence P_N≃∏ᵢP_{pᵢ^{aᵢ}}, and τ becomes the componentwise translation. We first determine the complete cycle lengths and counts in a single component.
6. Fix a prime p and a≥1. Modulo pᵃ a residue is a unit exactly when its integer representative is not divisible by p: Bézout gives the inverse in one direction, and reduction modulo p excludes an inverse in the other. A unimodular row has a unit coordinate, because otherwise reduction modulo p would annihilate every linear combination. Normalization therefore gives exactly two disjoint charts [1:t] for arbitrary t and [s:1] for s divisible by p. The coordinate 1 forces uniqueness within a chart; divisibility of the first coordinate separates the charts.
7. Translation sends [1:t] to [1:t+1]. These pᵃ points form one cycle of length pᵃ: addition by n returns precisely when pᵃ∣n, and every residue can be reached by adding an integer. On the second chart, translation sends [s:1] to [s:1+s]=[s/(1+s):1]. The denominator is a unit because it is 1 modulo p.
8. For every n≥0, 1+ns is a unit, and induction gives τⁿ[s:1]=[s/(1+ns):1]. The induction step follows from s/(1+ns) divided by 1+s/(1+ns) being s/(1+(n+1)s). Uniqueness in this chart shows return to [s:1] exactly when s/(1+ns)=s, equivalently ns²=0 modulo pᵃ. Multiplication by the inverse of 1+ns preserves divisibility by every power of p, so each exact-valuation stratum is invariant.
9. The element s=0 is fixed. Every other s in the second chart has a unique exact valuation j with 1≤j<a: using its nonzero representative less than pᵃ, write s=pʲv with v not divisible by p, hence a unit modulo pᵃ. The return condition is pᵃ∣np^{2j}v², equivalent, since v is a unit, to pᵃ∣np^{2j}, and therefore to p^{max(a−2j,0)}∣n. The least positive return time is L_j=p^{max(a−2j,0)}.
10. There are p^{a−j} residues divisible by pʲ and p^{a−j−1} divisible by p^{j+1}, so the exact-valuation stratum has p^{a−j}−p^{a−j−1} elements. Each cycle in it has the same length L_j, so its number of cycles is this cardinality divided by L_j. When 2j<a this quotient is pʲ−p^{j−1}; when 2j≥a it is p^{a−j}−p^{a−j−1}. In both cases it equals φ(p^{min(j,a−j)}). Indeed, for b≥1 the residues coprime to pᵇ are exactly those not divisible by p, giving φ(pᵇ)=pᵇ−p^{b−1}.
11. Include the first-chart cycle as j=0 and the fixed element s=0 as j=a, each contributing φ(1)=1. The local cycle count is thus ∑_{j=0}^{a}φ(p^{min(j,a−j)}). Every local cycle length is a power of p, including the power p⁰=1.
12. Choose one local cycle in each prime-power component. Their lengths are powers of distinct primes and hence pairwise coprime. Given any tuple of positions within these cycles, Chinese remaindering on the iteration number gives n that reaches all positions simultaneously. Thus the product of the chosen cycles is one global cycle. Products of local cycles partition the product set, so the global cycle count is the product of the local cycle counts in step 11.
13. Totient is multiplicative on coprime positive integers: Bézout identifies units modulo m with residues coprime to m, and Chinese remaindering identifies units modulo a coprime product with pairs of units. The cardinality of the latter set is the product of the two cardinalities. Expand the product from step 12 using this multiplicativity. Each exponent tuple 0≤jᵢ≤aᵢ corresponds uniquely to a divisor d=∏ᵢpᵢ^{jᵢ} of N, and gcd(d,N/d)=∏ᵢpᵢ^{min(jᵢ,aᵢ−jᵢ)}. Thus its contribution is φ(gcd(d,N/d)), and the full sum is ∑_{d∣N}φ(gcd(d,N/d))=ModularCurve.cuspCount N. Step 3 transfers this count to the quotient by MulAction.orbitRel for the subgroup generated by T, as claimed.

## Key steps

1. Use row lifting to identify right cosets with finite unimodular row classes.
2. Transfer the required orbits to cycles of [r:s]↦[r:r+s].
3. Decompose row classes and translation using Chinese remaindering.
4. Compute prime-power cycles in the two charts.
5. Count exact-valuation strata and divide by their common periods.
6. Combine local cycles using their pairwise coprime lengths.
7. Expand the product using multiplicativity of totient and the divisor exponent parametrization.

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
