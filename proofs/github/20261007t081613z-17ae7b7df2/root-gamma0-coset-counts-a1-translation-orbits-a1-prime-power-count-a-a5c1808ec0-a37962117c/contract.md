<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.translation_charts-a1.unique_row_parameter-a1 -->

## Theorem `Submission.p10_17ae7b7d_tchart_unique_row`

Let p and a be natural numbers with p prime and a≥1. Put R=ℤ/(p^a)ℤ and B={z∈R : p divides z.val}, using the canonical nonnegative representative. For every r,s∈R satisfying xr+ys=1 for some x,y∈R, there exists exactly one c∈R⊔B with the following property: if c=inl(t), there is u∈Rˣ such that r=u and s=ut; if c=inr(z), there is u∈Rˣ such that r=uz and s=u.

Node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.translation_charts-a1.unique_row_parameter-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/482

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_tchart_unique_row`

```lean
∀ (p a : ℕ), Nat.Prime p → 1 ≤ a → let R := ZMod (p ^ a); ∀ r s : R, (∃ x y : R, x * r + y * s = 1) → ∃! c : R ⊕ {z : R // p ∣ z.val}, match c with | Sum.inl t => ∃ u : Rˣ, r = (u : R) ∧ s = (u : R) * t | Sum.inr z => ∃ u : Rˣ, r = (u : R) * z.1 ∧ s = (u : R)
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

- Parent DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.translation_charts-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.translation_charts-a1.unique_row_parameter-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put M=p^a. Since p is prime and a≥1, p≥2, M>1, and p divides M. Reduction of integer representatives modulo p therefore defines a unital ring homomorphism ρ:R→ℤ/pℤ: representatives differing by a multiple of M also differ by a multiple of p. Every x∈R is represented by x.val, so ρ(x)=0 exactly when p divides x.val.
2. An element x∈R is a unit exactly when p does not divide x.val. If p does not divide x.val, then gcd(x.val,M)=1: any prime dividing both would divide p^a, hence equal p, a contradiction. A Bezout identity for x.val and M reduces to an inverse for x in R. Conversely, if p divides x.val and x had an inverse, applying ρ to their product would give 0=1 in ℤ/pℤ, impossible because p≥2.
3. Fix r,s and witnesses x,y with xr+ys=1. At least one of r,s is a unit. Otherwise step 2 gives ρ(r)=ρ(s)=0, and reducing the witness identity gives 0=1 in ℤ/pℤ.
4. If r is a unit, choose u∈Rˣ with value r and set t=(u⁻¹)s, where the inverse is taken in the unit group and then coerced into R. The unit identities give r=u and ut=s. Thus c=inl(t) satisfies the required property.
5. If r is not a unit, step 3 makes s a unit. Choose u∈Rˣ with value s and set z=(u⁻¹)r. Steps 1 and 2 give ρ(r)=0, hence ρ(z)=ρ(u⁻¹)ρ(r)=0. Therefore p divides z.val, so z determines an element of B. The unit identities give uz=r and u=s. Thus c=inr(z) satisfies the required property.
6. Prove uniqueness within each summand. If inl(t) and inl(t′) satisfy the property with unit witnesses u,v, then u=r=v as elements of R. The equations s=ut=vt′ therefore give ut=ut′; multiplication by u⁻¹ yields t=t′. If inr(z) and inr(z′) satisfy the property with witnesses u,v, then u=s=v. The equations r=uz=vz′ give uz=uz′; multiplication by u⁻¹ yields equality of the underlying ring elements. Subtype extensionality gives z=z′ in B.
7. Parameters from different summands cannot both satisfy the property. An inl parameter makes r the value of a unit. An inr parameter gives r=vz with z∈B, so ρ(r)=ρ(v)ρ(z)=0. By steps 1 and 2, r is then not a unit, a contradiction. Steps 4 and 5 establish existence, and steps 6 and 7 show that any two satisfying parameters are equal. This proves the asserted unique existence.

## Key steps

1. Construct reduction modulo p and identify its zero fiber using canonical representatives.
2. Characterize units modulo p^a by nondivisibility of the representative by p.
3. Reduce the unimodularity identity to prove that one coordinate is a unit.
4. Normalize by the first coordinate when it is a unit.
5. Otherwise normalize by the second coordinate and prove the resulting first coordinate belongs to B.
6. Cancel unit witnesses to establish uniqueness within each chart.
7. Separate the charts by whether the first coordinate is a unit.

## Reference use

### local-project

Queries:
- `rg -n 'IsUnimodularRow|unimodularRowSetoid|Gamma0_mem|isUnit_natCast_iff_not_dvd_pow|inv_coe_unit|natCast_zmod_val|SL2_inv_expl|leftCoset_eq_iff' project/Definitions/Def_ModularCurve_ProjectiveLine.lean mathlib/Mathlib/Data/ZMod/Basic.lean mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean mathlib/Mathlib/GroupTheory/Coset/Basic.lean`
- `rg -n 'normal.*form|chart.*equiv|existsUnique.*[Rr]ow|unique.*[Rr]ow' project/Definitions/Def_ModularCurve_ProjectiveLine.lean mathlib/Mathlib/Data/ZMod mathlib/Mathlib/NumberTheory/ModularForms`
- `sed -n '799,853p' .humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `sed -n '75,102p' mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Basic.lean`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Snapshot-relative commands above ran from the snapshot root. ProjectiveLine defines unimodular rows and common unit scaling, but that module is absent from the frozen imports; the new type therefore uses explicit witnesses. The normalization search found no relevant existing theorem. Pinned mathlib supplies the prime-power unit criterion, canonical-representative identity, agreement of ZMod inversion with unit inversion, Gamma0 membership, and the determinant-one inverse formula. Clean dependency pins, compatibility, and permitted transitive axioms were checked during the disposable interface diagnostics.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
