<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1.coprime_orbit_product-a1 -->

## Theorem `Submission.p10_17ae7b7d_ccm_coprime_orbit_product`

Let G be a group acting on sets X and Y, let g∈G, and let m,n be nonzero coprime natural numbers. Assume g^m·x=x for every x∈X and g^n·y=y for every y∈Y. Let H={g^z : z∈ℤ}, acting on X and Y by restriction and on X×Y diagonally. Then Nat.card((X×Y)/H)=Nat.card(X/H)·Nat.card(Y/H). No finiteness or nonemptiness assumption on X or Y is required.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1.coprime_orbit_product-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/453

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_ccm_coprime_orbit_product`

```lean
∀ (G X Y : Type) [Group G] [MulAction G X] [MulAction G Y] (g : G) (m n : ℕ) [NeZero m] [NeZero n], Nat.Coprime m n → (∀ x : X, (g ^ m) • x = x) → (∀ y : Y, (g ^ n) • y = y) → Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (X × Y))) = Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) X)) * Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) Y))
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

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1.coprime_orbit_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated group, actions, element, and periods. The action of g on each set is a permutation, with inverse given by the action of g⁻¹. On X, its m-th power is the identity by hypothesis, so every integer power of that m-th power is also the identity. Consequently, if integers a,b satisfy m∣a−b, then g^a·x=g^b·x for every x∈X. Indeed, writing a−b=mk and using the power and action laws expresses the additional action as that of (g^m)^k, which is the identity. The same argument applies to Y with period n.
2. Two points in the same H-orbit of X×Y have their respective coordinates in the same H-orbits, because g^t·(x,y)=(g^t·x,g^t·y) for every integer t.
3. Conversely, suppose x′=g^i·x and y′=g^j·y for integers i,j. Choose u,v∈ℤ with um+vn=1 and put t=ivn+jum. Then t−i=um(j−i) and t−j=vn(i−j). Step 1 therefore gives g^t·x=g^i·x=x′ and g^t·y=g^j·y=y′. Thus (x′,y′)=g^t·(x,y), so the pairs are in the same H-orbit. Together with step 2, this proves that diagonal orbit equivalence is exactly coordinatewise orbit equivalence.
4. Define a map from the diagonal orbit quotient to (X/H)×(Y/H) by sending the class of (x,y) to the pair of classes ([x],[y]). Step 2 proves that it is well-defined. Step 3 proves injectivity. It is surjective because any pair of quotient classes has representatives x,y, and the class of (x,y) maps to that pair. Hence the two quotient types are equivalent. This reasoning also covers empty sets, since then the relevant surjectivity assertion has no pair of classes to consider.
5. Apply invariance of Nat.card under equivalence and the identity Nat.card(U×V)=Nat.card(U)·Nat.card(V), with U=X/H and V=Y/H. This identity holds without finiteness assumptions: for finite U,V it is ordinary counting; if either is empty both sides vanish; otherwise an infinite factor makes the product infinite, and Nat.card of each infinite type is zero. The resulting equality is precisely the claimed formula.

## Key steps

1. Show that congruent integer exponents induce identical actions modulo each prescribed period.
2. Project a diagonal orbit relation to the two coordinate orbit relations.
3. Use an explicit Bézout CRT exponent to combine two coordinate orbit relations.
4. Obtain a bijection between the diagonal orbit quotient and the product of coordinate orbit quotients.
5. Apply Nat.card invariance and the unrestricted product-cardinality formula.

## Reference use

### local-project

Queries:
- `ProjectiveLine|Unimodular|unimodular|cusp|orbit`
- `def chineseRemainder|theorem.*chineseRemainder|castHom|chineseRemainder.*apply`
- `def Gamma0|mem_Gamma0|Gamma0.*(map|inf|mul)|T_zpow|T_pow`
- `orbit.*[Cc]oprime|[Cc]oprime.*orbit|Gamma0.*[Cc][Rr][Tt]|Gamma0.*(equivProd|prodEquiv)|cuspCount.*mul`
- `p10_17ae7b7d_ccm_(coset_crt_equivariant|translation_period|coprime_orbit_product)`
- `python3 /tmp/p10_ccm_decomposition_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/SetTheory/Cardinal/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/Submission.original.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/ParentAssembly.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/ccm-split-muk3reqj/report.json`
- `/runtime/operator-header-policy-v1/policy.json`

The clean snapshots matched project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine compiler dependencies matched their pins with clean tracked files. Relevant infrastructure includes ZMod.chineseRemainder, Gamma0_mem, left-coset actions, and Nat.card_prod without finiteness assumptions. The targeted search found no matching equivariant Gamma0 CRT theorem or coprime orbit-product theorem. The separate projective-line module is outside the frozen imports, so the proposed interfaces use existing cosets and group actions. The frozen proof base c77074cc2682d4bf219f2909b6b4767445f7f7bc already contains the accepted unimodular-row lifting theorem. All three exact child types elaborated after import Submission; matrix multiplication, left-coset action, diagonal product action, and subgroup restriction passed explicit instance probes. Their conditional composition proved the exact parent type. The proposed names were absent from the DAG, handoffs, and imported environment. Audited interfaces, the existing lifting theorem, and relevant library declarations use only propext, Classical.choice, and Quot.sound. Disposable compiler copies followed policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: only lines 10–12 were omitted, all 56 targets passed Lean absence checks, and reversible original/build hashes are recorded. Concurrent changes to the working Submission body triggered a housekeeping assertion; all compiler checks used the frozen copy, and the original contract and current Submission header were rechecked successfully. These are interface diagnostics, not comparator acceptance of the proposed proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/636

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
