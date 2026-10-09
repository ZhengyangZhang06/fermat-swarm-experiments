<!-- theorem-id: fermat-p10/root.gamma0_norm_vanishing-a1.local_multiplier_order-a1 -->

## Theorem `Submission.p10_17ae7b7d_norm_local_multiplier_order`

Let g, ψ, J:ℂ→ℂ and v∈ℂ. Assume all three functions are analytic at v, analyticOrderAt g v ≠ ⊤, ψ(v)=v, and ψ′(v)≠0. Suppose there exists a real r>0 such that g(ψ(z))=J(z)g(z) whenever ‖z−v‖<r. Then ψ′(v) raised to analyticOrderNatAt g v equals J(v).

Node: `root.gamma0_norm_vanishing-a1.local_multiplier_order-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/375

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_norm_local_multiplier_order`

```lean
∀ (g ψ J : ℂ → ℂ) (v : ℂ), AnalyticAt ℂ g v → analyticOrderAt g v ≠ ⊤ → AnalyticAt ℂ ψ v → ψ v = v → deriv ψ v ≠ 0 → AnalyticAt ℂ J v → (∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z - v‖ < r → g (ψ z) = J z * g z) → (deriv ψ v) ^ analyticOrderNatAt g v = J v
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

- Parent DAG node: `root.gamma0_norm_vanishing-a1`
- Child DAG node: `root.gamma0_norm_vanishing-a1.local_multiplier_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix g, ψ, J and v satisfying the hypotheses, and put m=analyticOrderNatAt g v and λ=ψ′(v). AnalyticAt.analyticOrderNatAt_eq_iff, applied to the analyticity and finite-order hypotheses for g, gives a function b analytic near v with b(v)≠0 and g(z)=(z−v)^m b(z) throughout a neighborhood of v.
2. Expand ψ in a convergent Taylor series at v. Its constant coefficient is ψ(v)=v and its linear coefficient is λ. Removing the constant term and dividing the series by z−v produces an analytic function d near v such that ψ(z)−v=(z−v)d(z) and d(v)=λ. Explicitly, if ψ(v+h)=v+∑_{n≥1}c_n h^n, then d(v+h)=∑_{n≥0}c_{n+1}h^n. The shifted series converges on every smaller disk, including at h=0, and c_1=λ.
3. Choose a sufficiently small disk centered at v on which the factorization of g, the factorization of ψ−v, and the assumed equivariance identity all hold. Continuity of ψ and ψ(v)=v allow this disk to be shrunk further so that ψ(z) lies in the neighborhood where the factorization of g is valid. On this disk, substitution into equivariance gives (z−v)^m d(z)^m b(ψ(z))=J(z)(z−v)^m b(z).
4. For z≠v in this disk, the complex number (z−v)^m is nonzero, including when m=0. Cancel it to obtain d(z)^m b(ψ(z))=J(z)b(z).
5. Each side of this last identity is continuous at v. Taking z→v through the punctured disk gives λ^m b(v)=J(v)b(v), because d(v)=λ and ψ(v)=v. Such a punctured limit exists since every complex disk of positive radius contains points distinct from its center approaching the center. Finally b(v)≠0 permits cancellation, giving λ^m=J(v), exactly the asserted identity.

## Key steps

1. Factor the finite-order germ of g into a power times a nonvanishing analytic factor.
2. Factor ψ(z)−v as (z−v)d(z), with d(v)=ψ′(v).
3. Choose a common neighborhood supporting both factorizations and equivariance.
4. Substitute and cancel the power away from v.
5. Pass to the limit at v and cancel the nonzero leading coefficient.

## Reference use

### local-project

Queries:
- `analyticOrder.*(prod|mul|comp)|eqOn_zero|frequently_eq|isolated`
- `gamma0_norm|cyclic.*norm|elliptic.*order|valence`
- `norm.*prod|prod.*norm|rotation|root.*unity|IsPrimitiveRoot`
- `deriv.*analyticOrderNatAt|analyticOrderNatAt.*deriv|analyticOrder.*multiplier`
- `p10_17ae7b7d_norm_cyclic_product_descent|p10_17ae7b7d_norm_local_multiplier_order`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/OfScalars.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Order.lean supplies local factorization, analyticOrderNatAt_mul, and preservation of order under composition with nonzero derivative; IsolatedZeros.lean supplies the identity principle and nonvanishing-product infrastructure. OfScalars.lean supports convergent scalar power series. Log.lean:160 supplies exp_two_pi_mul_I_mul_div_eq_one_iff. The targeted searches found no matching cyclic-product descent or local multiplier-order theorem. No proposed-name collision was found in the local DAG or searched worktrees. All pinned dependency checkouts were clean. The exact proposed types and cited order, identity, and exponential lemmas had only propext, Classical.choice, and Quot.sound in their transitive axiom lists.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/471

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
