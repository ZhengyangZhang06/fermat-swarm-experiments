<!-- theorem-id: fermat-p10/root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.orbit_product_order-a1 -->

## Theorem `Submission.p10_17ae7b7d_cpd_orbit_product_order`

Let w be a positive natural number, let ζ∈ℂ satisfy ζ^w=1, and let A:ℂ→ℂ be analytic at zero with analyticOrderAt A 0≠⊤. Define P(t)=∏_{j=0}^{w−1}A(ζ^j t). Then P is analytic at zero, analyticOrderAt P 0≠⊤, analyticOrderNatAt P 0=w·analyticOrderNatAt A 0, and P(ζt)=P(t) for every t∈ℂ.

Node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.orbit_product_order-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/403

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/455, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/456

## Lean problem

Declaration: `Submission.p10_17ae7b7d_cpd_orbit_product_order`

```lean
∀ (w : ℕ) (ζ : ℂ) (A : ℂ → ℂ), 0 < w → ζ ^ w = 1 → AnalyticAt ℂ A 0 → analyticOrderAt A 0 ≠ ⊤ → let P : ℂ → ℂ := fun t => ∏ j ∈ Finset.range w, A (ζ ^ j * t); AnalyticAt ℂ P 0 ∧ analyticOrderAt P 0 ≠ ⊤ ∧ analyticOrderNatAt P 0 = w * analyticOrderNatAt A 0 ∧ ∀ t : ℂ, P (ζ * t) = P t
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

- Parent DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1`
- Child DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.orbit_product_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a positive natural number w, a complex number ζ with ζ^w=1, and a complex-valued function A analytic at zero with finite analytic order. Define P(t)=∏_{j=0}^{w−1} A(ζ^j t). Since w>0, ζ=0 would imply ζ^w=0, contradicting ζ^w=1. Thus ζ≠0.
2. Put m=analyticOrderNatAt A 0. The local order characterization gives a function b analytic at zero, with b(0)≠0, such that A(t)=t^m b(t) on a neighborhood of zero. This follows from AnalyticAt.analyticOrderNatAt_eq_iff using the given finite-order hypothesis.
3. For each j<w, the linear map t↦ζ^j t is analytic, is continuous, and takes zero to zero. Consequently A(ζ^j t) and b(ζ^j t) are analytic at zero, and the identity from step 2 applies at ζ^j t throughout a neighborhood of zero. Intersect these finitely many neighborhoods. On the resulting neighborhood all these identities hold simultaneously. The finite product defining P is analytic at zero.
4. Define D(t)=∏_{j=0}^{w−1}(ζ^(j*m) b(ζ^j t)). It is analytic at zero, and each factor of D(0) is nonzero because ζ≠0 and b(0)≠0. Therefore D(0)≠0. On the neighborhood from step 3, expanding (ζ^j t)^m and multiplying the w factors gives P(t)=t^(w*m)D(t).
5. Apply AnalyticAt.analyticOrderAt_eq_natCast to P and the factorization in step 4. It gives analyticOrderAt P 0=(w*m : ℕ∞). This is finite, and taking its natural value gives analyticOrderNatAt P 0=w*m.
6. For every complex t, associativity and commutativity give P(ζt)=∏_{j=0}^{w−1} A(ζ^(j+1)t). Its exponents are 1 through w. The last factor is A(t), since ζ^w=1, and the factors with exponents 1 through w−1 are the same as in P(t). Permuting factors therefore gives P(ζt)=P(t). When w=1 both intervening products are empty and this argument still applies. Combining steps 3, 5, and 6 proves all conclusions.

## Key steps

1. Deduce ζ≠0 from w>0 and ζ^w=1.
2. Factor A(t)=t^m b(t) locally with b analytic and b(0)≠0.
3. Pull back this factorization along the finitely many linear maps t↦ζ^j t.
4. Obtain P(t)=t^(w*m)D(t), with D analytic and D(0)≠0, and apply the order characterization.
5. Reindex the cyclic product to prove P(ζt)=P(t) globally.

## Reference use

### local-project

Queries:
- `analyticOrderNatAt.*(comp|mul|prod|pow)|analyticOrderAt.*(comp|mul|prod|pow)|exp_two_pi_mul_I_mul_div_eq_one_iff`
- `invariant|divisib|comp_pow|iterate.*coeff`
- `eq_formalMultilinearSeries|unique|coeff|eq_of`
- `hasFPowerSeries|analyticAt|summable.*radius|le_radius`
- `cyclic.*(product|prod|descent)|rotation.*(descent|invariant)|analytic.*(root.of.unity|comp_pow)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/OfScalars.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Uniqueness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/ConvergenceRadius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`

The clean snapshot matches project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Order.lean supplies local factorization, analyticOrderAt_congr, analyticOrderAt_pow, and AnalyticAt.analyticOrderAt_comp. Uniqueness.lean supplies uniqueness of one-variable analytic expansions. OfScalars.lean and ConvergenceRadius.lean support scalar series and convergence-radius bounds from summability. Log.lean:160 supplies the exponential divisibility criterion. Targeted searches found no matching analytic rotation-descent theorem. All nine dependency checkouts match their pins and are clean. The checked proposition definitions and cited library declarations depend only on propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/551

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
