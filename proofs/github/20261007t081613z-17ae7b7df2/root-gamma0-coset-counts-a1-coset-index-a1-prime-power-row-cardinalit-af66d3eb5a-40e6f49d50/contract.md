<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1.unimodular_iff_unit_coordinate-a1 -->

## Theorem `Submission.p10_17ae7b7d_uce_unimodular_iff_unit_coord`

For natural numbers p and a with p prime and 0 < a, put R = ℤ/p^aℤ. For every r,s ∈ R, there exist x,y ∈ R with xr + ys = 1 if and only if r is a unit or s is a unit.

Node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1.unimodular_iff_unit_coordinate-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/485

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_uce_unimodular_iff_unit_coord`

```lean
∀ (p a : ℕ), p.Prime → 0 < a → ∀ r s : ZMod (p ^ a), (∃ x y : ZMod (p ^ a), x * r + y * s = 1) ↔ IsUnit r ∨ IsUnit s
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

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1.unimodular_iff_unit_coordinate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a prime p, a positive natural number a, and r,s in R = ℤ/qℤ, where q = p^a. Since p ≥ 2 and a ≥ 1, q ≥ 2 and p divides q. Reduction of integer representatives modulo p therefore gives a well-defined unital ring homomorphism ρ : R → ℤ/pℤ. The target is nontrivial because p ≥ 2.
2. For any natural number k not divisible by p, gcd(k,q) = 1. The gcd is positive because q > 0. If it exceeded 1, it would have a prime divisor ℓ. Then ℓ would divide k and p^a. Repeated application of the prime-divides-product property implies ℓ divides p; since p is prime, ℓ = p, contradicting p not dividing k. Bézout's identity now supplies integers b,c with bk + cq = 1. Reducing this identity modulo q gives b̄k̄ = 1. Commutativity also gives k̄b̄ = 1, so k̄ is a unit in R.
3. If p divides k, then ρ(k̄) = 0. A unital ring homomorphism sends a unit to a unit, while zero is not a unit in the nontrivial ring ℤ/pℤ: an inverse of zero would imply 0 = 1. Consequently k̄ is not a unit. Together with step 2 this proves that k̄ is a unit exactly when p does not divide k.
4. Suppose x r + y s = 1 for some x,y in R. If neither r nor s were a unit, choose their natural representatives k,l between 0 and q−1. Step 3 together with step 2 implies p divides k and p divides l. Thus ρ(r) = ρ(s) = 0. Applying ρ to the displayed equation gives ρ(x)·0 + ρ(y)·0 = 1, hence 0 = 1, a contradiction. Therefore r is a unit or s is a unit.
5. Conversely, if r is a unit, let b be its inverse and take x = b and y = 0; then x r + y s = 1. If s is a unit, let c be its inverse and take x = 0 and y = c; the same equation follows. These two cases prove the reverse implication and hence the asserted equivalence.

## Key steps

1. Construct reduction modulo p using p ∣ p^a and note its nontrivial target.
2. Prove the residue-unit criterion using coprimality and Bézout in one direction and reduction modulo p in the other.
3. Reduce a putative unimodular equation with two nonunit coordinates to 0 = 1.
4. Use the inverse of a unit coordinate to construct Bézout coefficients.

## Reference use

### local-project

Queries:
- `unimodularRow|UnimodularRow|ProjectiveLine`
- `unimodularRow|UnimodularRow|ProjectiveLine|prime_pow|isUnit_iff`
- `prime_power|primePower|chart|nonunit|isUnit_or|IsLocalRing`
- `Quot.eq|eqvGen|EqvGen|exact`
- `eqvGen_iff|EqvGen.*iff|eqvGen_eq|Equivalence.*eqvGen`
- `python3 .humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/unit-charts-split-ky342xt0/run.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Quot.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Logic/Relation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/unit-charts-split-ky342xt0/report.json`

The pinned mathlib supplies ZMod.isUnit_natCast_iff_not_dvd_pow, Quot.eq, and Equivalence.eqvGen_iff. Their transitive axiom checks contain only propext, Classical.choice, and Quot.sound, or no axioms. The inspected project ProjectiveLine file defines unimodular rows and the unit-scaling setoid, but contains no matching prime-power chart theorem; its setoid is absent under the frozen imports, so the proposed types spell out their subtypes and relation. Both exact child types elaborated after import Submission using a disposable copy of proof-base commit 6134a09ac36170885efc4ca0bfae953f03a4e698. The diagnostic verified nine clean pinned dependencies, the required policy digest, reversible omission of precisely lines 10–12, and absence of all 56 omitted targets. Proposed names were absent from the imported environment and active DAG. These are interface diagnostics, not comparator acceptance of any proof.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
