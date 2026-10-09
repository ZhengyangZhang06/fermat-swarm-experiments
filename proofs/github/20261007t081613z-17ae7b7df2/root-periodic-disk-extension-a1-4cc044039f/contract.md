<!-- theorem-id: fermat-p10/root.periodic_disk_extension-a1 -->

## Theorem `Submission.p10_17ae7b7d_periodic_disk_extension`

Let w>0 be real and g:ℂ→ℂ be holomorphic on ℍ={z:Im z>0}, with a nonzero value there. Suppose g(z+w)=g(z) on ℍ and there exist real C,Y such that ‖g(z)‖≤C whenever z∈ℍ and Im z≥Y. Then there exists A:ℂ→ℂ holomorphic on |q|<1 such that g(z)=A(exp(2πiz/w)) on ℍ and analyticOrderAt A 0≠⊤. For this same A, if additionally for every ε>0 there is a real Yε such that ‖g(z)‖≤ε whenever z∈ℍ and Im z≥Yε, then analyticOrderNatAt A 0≥1.

Node: `root.periodic_disk_extension-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/412, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/413, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/414

## Lean problem

Declaration: `Submission.p10_17ae7b7d_periodic_disk_extension`

```lean
∀ (w : ℝ) (g : ℂ → ℂ), 0 < w → DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → (∃ z : ℂ, 0 < z.im ∧ g z ≠ 0) → (∀ z : ℂ, 0 < z.im → g (z + (w : ℂ)) = g z) → (∃ C Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im → ‖g z‖ ≤ C) → ∃ A : ℂ → ℂ, DifferentiableOn ℂ A (Metric.ball (0 : ℂ) 1) ∧ (∀ z : ℂ, 0 < z.im → g z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / (w : ℂ)))) ∧ analyticOrderAt A 0 ≠ ⊤ ∧ ((∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im → ‖g z‖ ≤ ε) → 1 ≤ analyticOrderNatAt A 0)
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

- Parent DAG node: `root`
- Child DAG node: `root.periodic_disk_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put q_w(z)=exp(2πiz/w). The complex exponential is nonzero and has modulus exp(−2π Im z/w). Since w>0, q_w maps ℍ into the punctured unit disk. Conversely, for 0<|q|<1 choose L with exp L=q and put z=wL/(2πi). The modulus identity gives |q|=exp(−2π Im z/w), so Im z>0 and q_w(z)=q. Existence of L follows from Complex.exp_log for q≠0 in the pinned Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:41. The same modulus identity shows that all preimages of q have height −w log|q|/(2π), which tends to infinity as q tends to zero.

2. The exponential equality criterion Complex.exp_eq_exp_iff_exists_int, in the same pinned file at line 171, says that two preimages of q differ by nw for an integer n. Periodicity implies invariance under nonnegative integer shifts by induction. Applying periodicity at z−w, which still belongs to ℍ, gives invariance under a negative shift; induction handles every negative integer. Consequently A₀(q)=g(z), for any preimage z of q, is well-defined on the punctured disk.

3. Fix q₀ in the punctured disk and choose L₀ with exp L₀=q₀. For |q−q₀|<|q₀| define L(q)=L₀+∑_{n≥1}(−1)^{n+1}((q−q₀)/q₀)ⁿ/n. On every smaller closed disk this series and its derivative series converge uniformly by geometric bounds. Thus L is holomorphic and the geometric-series identity gives L′(q)=1/q. The derivative of exp(L(q))/q is zero. Integrating this derivative along segments in the disk shows the quotient is constant; its value at q₀ is 1. Hence exp L(q)=q. Restricting to a neighborhood also contained in |q|<1, the function wL(q)/(2πi) is a holomorphic preimage taking values in ℍ. The identity A₀(q)=g(wL(q)/(2πi)) proves that A₀ is holomorphic away from zero.

4. The elementary calculus used in step 3 is justified as follows. If a power series converges at radius R and 0<r<R, its coefficients satisfy |aₙ|Rⁿ≤K for some K. Each fixed derivative series on the radius-r disk is bounded by a constant times nᵈ(r/R)ⁿ, a summable series by the ratio test. Uniform convergence on smaller disks therefore permits termwise differentiation, obtained by applying the fundamental theorem to polynomial partial sums along segments and taking uniform limits. The fundamental theorem used here is intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le in the pinned Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1140. Continuous derivatives on the compact parametrizing intervals are integrable. This also justifies recovering Taylor coefficients by repeated differentiation.

5. Choose a positive height larger than the boundedness threshold Y. The height formula in step 1 gives r>0 such that r<1 and |A₀(q)|≤M=max(C,0) whenever 0<|q|<r. Define B(q)=q²A₀(q) off zero in the unit disk, and B(0)=0. Near zero, |B(q)|≤M|q|² and |B(q)/q|≤M|q|. These estimates prove continuity at zero and complex differentiability there with derivative zero. Away from zero B is holomorphic, so B is holomorphic throughout the unit disk.

6. Holomorphy on a neighborhood of zero supplies a convergent Taylor series, by DifferentiableOn.analyticAt in the pinned Mathlib/Analysis/Complex/CauchyIntegral.lean:625. Since B(0)=B′(0)=0, its constant and linear coefficients vanish. Dividing the remaining series by q² produces a holomorphic function near zero agreeing with A₀ off zero. Patching it with A₀ gives a holomorphic A on the unit disk. Extend A by zero outside that disk. These values outside the disk affect none of the local claims. By construction g(z)=A(q_w(z)) for every z∈ℍ.

7. We establish the nonzero germ and finite order. For a holomorphic function h on a connected open set, a first nonzero Taylor coefficient of degree m at v gives h(q)=(q−v)ᵐb(q), where b is holomorphic and b(v)≠0. On a smaller disk b is nowhere zero, so this disk contains at most one zero of h. Let E consist of points near which h vanishes identically. E is relatively open. At a point outside E the Taylor series cannot have all coefficients zero, so the preceding factorization gives a neighborhood disjoint from E; hence its complement is relatively open too. If h has a nonzero value, connectedness forces E to be empty. Apply this to A on the connected unit disk: the nonzero value of g supplies a nonzero value of A. Therefore A has a first nonzero coefficient at zero. Its exponent is unique, since dividing two proposed factorizations by the smaller power and taking the limit at zero would otherwise force a nonzero leading factor to vanish. The characterization AnalyticAt.analyticOrderAt_eq_natCast in Mathlib/Analysis/Analytic/Order.lean:86 identifies this finite exponent with analyticOrderAt, proving analyticOrderAt A 0≠⊤.

8. Finally suppose the additional decay assumption holds. Given ε>0, choose its decay height and then restrict |q| so that every preimage lies above this height, using step 1. Thus |A₀(q)|≤ε for all sufficiently small nonzero q, proving A₀(q)→0 at zero. Continuity of the already chosen extension gives A(0)=0. Its finite first nonzero coefficient consequently has degree at least 1. AnalyticAt.analyticOrderNatAt_eq_iff in the pinned Mathlib/Analysis/Analytic/Order.lean:101 identifies that degree with analyticOrderNatAt A 0, giving the required conditional conclusion for this same A.

## Key steps

1. Describe the exponential map onto the punctured disk and its integer-period fibers.
2. Use periodicity to define a single-valued descended function.
3. Construct local logarithms and prove holomorphy of the descended function.
4. Transfer the high-half-plane bound to a punctured neighborhood of zero.
5. Apply the q² construction and Taylor division to remove the puncture.
6. Use connectedness and the identity principle to prove a nonzero germ and finite order.
7. Use decay to show the extension vanishes at zero and has positive order.

## Reference use

### local-project

Queries:
- `rg -n 'def (genusFormula|nuTwo|nuThree|cuspCount|dedekindPsi)|valence|gamma0_coset_counts|periodic_disk_extension|gamma0_norm_vanishing|level_one_valence_inequality' <snapshot>/project/Definitions <snapshot>/mathlib/Mathlib/NumberTheory/ModularForms`
- `analyticOrderAt_eq_natCast|analyticOrderNatAt_eq_iff|theorem DifferentiableOn.analyticAt|isExactOn_ball|exp_two_pi_mul_I_mul_div_eq_one_iff|exp_eq_exp_iff_exists_int|isZeroAtImInfty_iff|mdifferentiable_iff|SL_slash_def|SL_slash_apply|def IsZeroAt|def IsCusp|def IsParabolic|integral_eq_sub_of_hasDerivAt_of_le`
- `gamma0_coset_counts|periodic_disk_extension|gamma0_norm_vanishing|level_one_valence_inequality|theorem.*[Vv]alence|lemma.*[Vv]alence`
- `rg -n --hidden --no-ignore -g dag.json 'p10_17ae7b7d_(gamma0_coset_counts|periodic_disk_extension|gamma0_norm_vanishing|level_one_valence_inequality)' /mnt/data/zhengyang-workspace/fermat-swarm-projects`
- `git rev-parse HEAD; git status --porcelain --untracked-files=no`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o TargetAbsence.olean TargetAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o ChildTypes.olean ChildTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Algebra/Group/Subgroup/Actions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.agents/skills/frozen-header-policy-evidence/evidence.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/operator-approved-header-policy-20261008/controller-compatibility-report.json`
- `/tmp/p10-split-interface-5bnnjwsk/report.json`
- `/tmp/p10-split-interface-5bnnjwsk/TargetAbsence.lean`
- `/tmp/p10-split-interface-5bnnjwsk/ChildTypes.lean`
- `/tmp/p10-split-interface-5bnnjwsk/ChildTypes.log`

The snapshot pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; fresh Git checks matched both revisions and found clean tracked snapshot trees and all nine dependency checkouts matching their pins. The numerical definitions, quotient actions, real-image subgroup coercion, cusp condition, and analytic-order interfaces match the proposed statements. Searches found no existing versions of the four helpers or a named valence theorem in the searched Definitions and modular-form sources, and no conflicting helper-name reservation in the local DAGs. All four literal types compiled after import Submission in a fresh disposable context. Reflexivity probes verified left multiplication on cosets, restriction to the subgroup generated by T, the real-image coercion, and matrix multiplication for S*T. The four type definitions and the selected imported declarations reported only propext, Classical.choice, and Quot.sound. Policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 was checked against its matching entry. Only original lines 10–12 were omitted in the disposable compiler copy; Lean confirmed all 56 targets absent. Original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and derived hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539 were recorded with exact omitted lines and reversible reconstruction. Original contract and Submission remained byte-identical. These are interface diagnostics, not child-proof or comparator acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/495

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
