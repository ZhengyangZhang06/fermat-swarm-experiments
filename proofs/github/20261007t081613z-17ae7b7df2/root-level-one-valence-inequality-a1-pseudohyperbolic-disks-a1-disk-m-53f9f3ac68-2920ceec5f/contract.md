<!-- theorem-id: fermat-p10/root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1.mobius_upper_half_plane_bijection-a1 -->

## Theorem `Submission.p10_17ae7b7d_phdisk_mobius_bijon`

Let a,b,c,d be real numbers satisfying ad−bc=1. Define H={z∈ℂ : Im(z)>0} and the total complex function M(z)=(az+b)/(cz+d), with real coefficients embedded in ℂ. Then M maps H into H, is injective on H, and is surjective from H onto H.

Node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1.mobius_upper_half_plane_bijection-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/491

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_phdisk_mobius_bijon`

```lean
∀ (a b c d : ℝ), a * d - b * c = 1 → Set.BijOn (fun z : ℂ => ((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im}
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
- Child DAG node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1.mobius_upper_half_plane_bijection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix real a,b,c,d with ad−bc=1. Set H={z∈ℂ : Im(z)>0}, Q(z)=cz+d, M(z)=(az+b)/Q(z), P(w)=−cw+a, and N(w)=(dw−b)/P(w). All real coefficients in these expressions are viewed as complex numbers.
2. First consider arbitrary real α,β,γ,δ satisfying αδ−βγ=1, and x=u+it with t>0. Put R(x)=γx+δ. If γ≠0, then Im(R(x))=γt≠0, hence R(x)≠0. If γ=0, the determinant equation gives αδ=1, so δ≠0 and R(x)=δ≠0. Thus R(x) is nonzero in either case.
3. For these same arbitrary coefficients, multiplication by the conjugate denominator gives Im((αx+β)/R(x))=[αt(γu+δ)−(αu+β)γt]/‖R(x)‖². The numerator is (αδ−βγ)t=t. Since R(x)≠0, its squared norm is positive, so this imaginary part is positive. Consequently every real determinant-one coefficient quadruple defines a map from H into H, with nonzero denominator there.
4. Apply steps 2–3 to (a,b,c,d). This proves Q(z)≠0 and M(z)∈H for every z∈H. Apply them also to (d,−b,−c,a), whose determinant is da−(−b)(−c)=ad−bc=1. This proves P(w)≠0 and N(w)∈H for every w∈H.
5. For z∈H, expansion gives d(az+b)−b(cz+d)=(ad−bc)z=z and −c(az+b)+a(cz+d)=ad−bc=1. Division by the nonzero Q(z) therefore gives dM(z)−b=z/Q(z) and P(M(z))=−cM(z)+a=1/Q(z). In particular this latter denominator is nonzero, and N(M(z))=(z/Q(z))/(1/Q(z))=z.
6. For w∈H, expansion gives a(dw−b)+b(−cw+a)=(ad−bc)w=w and c(dw−b)+d(−cw+a)=ad−bc=1. Division by the nonzero P(w) gives aN(w)+b=w/P(w) and Q(N(w))=cN(w)+d=1/P(w). Hence M(N(w))=(w/P(w))/(1/P(w))=w.
7. Step 4 proves that M maps H into H. If z₁,z₂∈H and M(z₁)=M(z₂), applying N and using step 5 gives z₁=z₂, proving injectivity on H. For any w∈H, step 4 gives N(w)∈H and step 6 gives M(N(w))=w, proving surjectivity onto H. These three assertions are precisely the claimed set bijection.

## Key steps

1. Prove that a real determinant-one linear denominator cannot vanish at a point with positive imaginary part.
2. Compute the transformed imaginary part as the original imaginary part divided by the squared denominator norm.
3. Apply this calculation to the original and inverse coefficient quadruples.
4. Expand the numerators to establish N(M(z))=z on the upper half-plane.
5. Expand the inverse numerators to establish M(N(w))=w there.
6. Deduce preservation, injectivity and surjectivity.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/586

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
