<!-- theorem-id: fermat-p10/root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1.mobius_ratio_norm_invariance-a1 -->

## Theorem `Submission.p10_17ae7b7d_phdisk_mobius_ratio_norm`

Let a,b,c,d be real numbers satisfying ad−bc=1, and let z,v∈ℂ satisfy Im(z)>0 and Im(v)>0. Define the total complex function M(x)=(ax+b)/(cx+d), with real coefficients embedded in ℂ. Then ‖(M(z)−M(v))/(M(z)−conj(M(v)))‖=‖(z−v)/(z−conj(v))‖.

Node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1.mobius_ratio_norm_invariance-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/491

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_phdisk_mobius_ratio_norm`

```lean
∀ (a b c d : ℝ) (z v : ℂ), a * d - b * c = 1 → 0 < z.im → 0 < v.im → let M : ℂ → ℂ := fun x => ((a : ℂ) * x + (b : ℂ)) / ((c : ℂ) * x + (d : ℂ)); ‖(M z - M v) / (M z - star (M v))‖ = ‖(z - v) / (z - star v)‖
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

- Parent DAG node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1.mobius_ratio_norm_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a,b,c,d,z,v satisfying the stated hypotheses. Write Q(x)=cx+d and M(x)=(ax+b)/Q(x). For either x=z or x=v, if c≠0 then Im(Q(x))=c Im(x)≠0, so Q(x)≠0. If c=0, the determinant equation implies ad=1 and therefore d≠0, again giving Q(x)≠0. Thus Q(z) and Q(v) are nonzero.
2. Because a,b,c,d are real, conjugation gives Q(conj(v))=conj(Q(v)) and M(conj(v))=conj(M(v)). Conjugation is an involution and sends zero to zero, so conj(Q(v))≠0.
3. For any complex x,y with Q(x)≠0 and Q(y)≠0, subtraction over the common denominator gives M(x)−M(y)=[(ax+b)(cy+d)−(ay+b)(cx+d)]/[Q(x)Q(y)]. Expanding the numerator cancels the acxy and bd terms and leaves (ad−bc)(x−y)=x−y. Hence M(x)−M(y)=(x−y)/(Q(x)Q(y)).
4. Apply step 3 to x=z,y=v to obtain M(z)−M(v)=(z−v)/(Q(z)Q(v)). Apply it to x=z,y=conj(v), using step 2, to obtain M(z)−conj(M(v))=(z−conj(v))/(Q(z)conj(Q(v))). The imaginary part of z−conj(v) is Im(z)+Im(v)>0, so z−conj(v)≠0. Since Q(z) and conj(Q(v)) are nonzero, the latter difference M(z)−conj(M(v)) is also nonzero.
5. Divide the two identities from step 4. Cancelling the nonzero factors Q(z), Q(v), conj(Q(v)) and z−conj(v) yields (M(z)−M(v))/(M(z)−conj(M(v)))=((z−v)/(z−conj(v)))·(conj(Q(v))/Q(v)). This cancellation does not require z−v to be nonzero.
6. Complex conjugation preserves norm, and Q(v)≠0 implies ‖Q(v)‖>0. Therefore ‖conj(Q(v))/Q(v)‖=‖conj(Q(v))‖/‖Q(v)‖=‖Q(v)‖/‖Q(v)‖=1. Taking norms in step 5 and using multiplicativity of the complex norm gives the required equality.

## Key steps

1. Establish nonvanishing of the denominators at z and v.
2. Use real coefficients to commute conjugation with the denominator and Möbius map.
3. Expand the numerator of a general difference of two Möbius values.
4. Specialize to v and its conjugate and verify nonvanishing of the ratio denominators.
5. Express the transformed ratio as the original ratio times conj(Q(v))/Q(v).
6. Show that the extra factor has norm one and take norms.

## Reference use

### local-project

Queries:
- `denom_ne_zero|im_smul|specialLinearGroup_apply|norm.*sub|conj|div.*im`
- `pseudohyperbolic|cross.ratio|norm.*conj.*denom`
- `def BijOn|theorem BijOn.mapsTo|theorem BijOn.surjOn|def SurjOn|structure BijOn|norm_conj|star_def`
- `rg -n --hidden --no-ignore -g 'dag.json' -g '!**/.lake/**' -g '!**/local-references/**' 'p10_17ae7b7d_phdisk_mobius_(bijon|ratio_norm)' /mnt/data/zhengyang-workspace/fermat-swarm-projects`
- `python3 /tmp/phdisk_mobius_decomposition_probe.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/Norm.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Complex/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/mobius-image-split-hyi3t56v/report.json`

The pinned sources provide denominator nonvanishing, the Möbius imaginary-part formula, the special-linear action, the related tanh_half_dist ratio identity, conjugation preserving norm, and the mapsTo/surjOn components of Set.BijOn. The targeted pseudohyperbolic/cross-ratio search found no matches in project/Definitions or the upper-half-plane directory. Both snapshots and all nine installed dependencies match their recorded revisions and are clean; the five inspected mathlib files match the installed sources byte-for-byte. Selected library axiom probes report only propext, Classical.choice and Quot.sound, or no axioms. Neither proposed name occurs in the searched DAGs or imported Lean environment. Both exact child types, complex-star/norm probes, and their composition into the unchanged parent type pass Lean after import Submission at proof base b4ff37aac322c66612cb8df5edb6a2d6a3a2dd6c. The diagnostic receipt records policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, reversible omission of only lines 10–12, original/build hashes, and a successful Lean absence probe for all 56 targets. These are decomposition diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/607

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
