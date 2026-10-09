<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.nonunit_cardinality-a1 -->

## Theorem `Submission.p10_17ae7b7d_ppr_nonunit_card`

For natural numbers p and a with p prime and 0 < a, the subtype of nonunits in ℤ/p^aℤ has natural cardinality p^(a−1): Nat.card {z : ZMod (p^a) // ¬ IsUnit z} = p^(a−1).

Node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.nonunit_cardinality-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/465

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p10_17ae7b7d_ppr_nonunit_card`

```lean
∀ (p a : ℕ), p.Prime → 0 < a → Nat.card {z : ZMod (p ^ a) // ¬ IsUnit z} = p ^ (a - 1)
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

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.nonunit_cardinality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a prime p and a positive integer a, and put q=p^a and b=p^(a−1). Since p≥2 and a=(a−1)+1, we have p>0, b>0, and q=p b>0. Each z∈Z/qZ has a unique natural representative z.val with 0≤z.val<q.
2. For any natural integer n, its residue in Z/qZ is a unit exactly when p does not divide n. If p divides n, reduction modulo p sends this residue to zero, which cannot be a unit because Z/pZ is nonzero. If p does not divide n, gcd(n,q)=1: a prime divisor ℓ of a larger gcd would divide p^a, hence divide p, hence equal p, contradicting p not dividing n. Bezout integers α,β with α n+β q=1 give an inverse after reduction modulo q. Applying the criterion to z.val shows that z is a nonunit exactly when p divides z.val.
3. Map the b natural integers k with 0≤k<b to nonunits by k↦(p k mod q). Since p k<p b=q, this residue has natural representative exactly p k. It is a nonunit by step 2, since p divides p k. Thus the map lands in the stated subtype, including when a=1 and b=1.
4. This map is injective: equal residues have equal natural representatives, so p k=p k′; cancellation of the positive natural number p yields k=k′.
5. This map is surjective: a nonunit z has p dividing z.val by step 2, hence z.val=p k for some natural k. The inequality p k=z.val<q=p b and p>0 imply k<b. Its image is z because casting z.val back into Z/qZ gives z. Equality of the subtype values gives equality of the subtype elements.
6. Consequently the nonunit subtype is in bijection with Fin b. Both sets are finite, and invariance of Nat.card under bijections gives Nat.card {z : ZMod(p^a) | z is not a unit}=Nat.card(Fin b)=b=p^(a−1).

## Key steps

1. Write p^a = p · p^(a−1), with both factors positive.
2. Identify nonunits with residues whose canonical representatives are divisible by p.
3. Send k < p^(a−1) to the residue of pk, whose representative is exactly pk.
4. Prove injectivity by equality of canonical representatives and cancellation of p.
5. Prove surjectivity by dividing the representative of a nonunit by p.
6. Transfer Nat.card along the bijection with Fin (p^(a−1)).

## Reference use

### local-project

Queries:
- `UnimodularRow|unimodularRow|ProjectiveLine|IsUnit|prime_pow`
- `ProjectiveLine.*(card|equiv)|card.*ProjectiveLine`
- `IsLocalRing.*ZMod|ZMod.*IsLocalRing|isLocalRing.*pow`
- `natCard|card \(|equivFin|natCast_zmod_val|val_lt|val_injective`
- `card_sum|card_congr|card_eq_fintype_card`
- `p10_17ae7b7d_ppr_(unit_chart_equiv|nonunit_card)`
- `python3 .humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/row-card-decomposition-g9q8sg1v/run.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/SetTheory/Cardinal/Finite.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/row-card-decomposition-g9q8sg1v/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/row-card-decomposition-g9q8sg1v/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/row-card-decomposition-g9q8sg1v/report.json`

The project defines the intended unit-scaling relation, but its ProjectiveLine module is absent from the frozen imports; the children therefore retain an explicit Quot expression. The project search found no matching projective-line chart-equivalence or cardinality theorem. Pinned mathlib provides ZMod.isUnit_natCast_iff_not_dvd_pow, canonical-representative lemmas, Nat.card_congr, Nat.card_sum and Nat.card_zmod. Their inspected transitive axiom sets contain only propext, Classical.choice and Quot.sound. Snapshot revisions and dependency pins were checked clean. Both proposed types elaborate after import Submission in a disposable copy of proof base 1e115a452fbc98bff8aaa6728679030b19690b46; explicit elaboration confirms IsUnit uses the monoid from ZMod.commRing. No proposed-name collision was found. The matching header policy digest was verified, all 56 omitted targets were checked absent by Lean, and exact omitted lines and reversible original/build hashes are recorded in report.json. Original sources remain unchanged. These are decomposition diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/554

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
