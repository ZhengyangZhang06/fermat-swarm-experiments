<!-- theorem-id: fermat-p10/root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1 -->

## Theorem `Submission.p10_17ae7b7d_idx_crt_row_card`

For each natural number m, let R_m=ℤ/mℤ and let P_m be the quotient of {(r,s)∈R_m² | ∃x,y∈R_m, xr+ys=1} by simultaneous multiplication by a unit of R_m. For every nonzero natural number N, let S be its finite set of prime divisors and e_p=N.factorization p. Then Nat.card P_N=∏_{p∈S} Nat.card P_(p^e_p).

Node: `root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/418

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/505, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/506

## Lean problem

Declaration: `Submission.p10_17ae7b7d_idx_crt_row_card`

```lean
∀ (N : ℕ) [NeZero N], let P : ℕ → Type := fun n => Quot (fun v w : {v : ZMod (n) × ZMod (n) // ∃ x y : ZMod (n), x * v.1 + y * v.2 = 1} => ∃ u : (ZMod (n))ˣ, (u : ZMod (n)) * v.1.1 = w.1.1 ∧ (u : ZMod (n)) * v.1.2 = w.1.2); Nat.card (P N) = N.primeFactors.prod (fun p => Nat.card (P (p ^ N.factorization p)))
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

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. For any commutative ring R, unit scaling preserves unimodularity: from xr+ys=1, coefficients xu⁻¹ and yu⁻¹ witness unimodularity of (ur,us). Identity, inverse, and product of units prove that scaling is an equivalence relation. Therefore each displayed Quot identifies exactly unit-scaled rows. For m≠0, the ring ℤ/mℤ is finite, so its unimodular-row subtype and quotient P_m are finite.
2. Fix N≠0. If N=1, the ring ℤ/ℤ has one element, with 0=1. Its sole row is unimodular, witnessed by x=y=0, so P_1 has one element. There are no prime divisors of 1, and the product on the right is the empty product 1. This proves the formula in this case.
3. Suppose N>1. Unique prime factorization gives N=∏_{p∈S}p^e_p, where S=N.primeFactors and e_p=N.factorization p>0. For completeness, existence of prime factorization follows by strong induction, factoring each composite number into two smaller factors greater than one. Uniqueness follows from Euclid's lemma: when p does not divide b, a Bézout identity for p,b multiplied by c shows that p dividing bc implies p dividing c. Applying this to products of primes and cancelling equal factors determines every exponent uniquely. Powers belonging to distinct primes are coprime, since a prime dividing both powers would have to equal both underlying primes.
4. Chinese remaindering gives a ring isomorphism Φ:ℤ/Nℤ≃∏_{p∈S}ℤ/p^e_pℤ. To see the construction, for coprime positive m,n choose integers u,v with um+vn=1. Prescribed residues A modulo m and B modulo n are realized modulo mn by Avn+Bum. If both m and n divide an integer k, write k=mt. Then n divides mt; multiplying the Bézout identity by t shows that n divides t, hence mn divides k. This proves injectivity as well as surjectivity of reduction to the two factors. Reduction preserves ring operations. Iterating over the pairwise coprime prime powers gives Φ.
5. Applying Φ coordinatewise sends a unimodular row to unimodular rows in every component, because its witnesses x,y project to witnesses in each factor. Conversely, given component rows (r_p,s_p) and witnesses x_p,y_p, the inverse of Φ assembles r,s,x,y. The equations x_p r_p+y_p s_p=1 in every component imply xr+ys=1 by injectivity of Φ.
6. Units also correspond componentwise. A global unit and its inverse project to inverse pairs. Conversely, a tuple of component units and the tuple of their inverses assemble through Φ⁻¹ to a global unit and its inverse. Consequently reduction defines a map F:P_N→∏_{p∈S}P_(p^e_p), independent of the representative row.
7. The map F is surjective: choose a representative row and unimodularity witnesses for each of the finitely many component classes, and assemble them as in step 5. It is injective: if two global rows give equal component classes, step 1 supplies a scaling unit u_p in each factor. Step 6 assembles these into one global unit u. The equalities between scaled coordinates hold after applying Φ in every component, hence hold globally by injectivity of Φ. The original rows thus represent the same class in P_N.
8. Therefore F is a bijection. All its component quotient types are finite by step 1 because p^e_p≠0. The cardinality of their finite product is the product of their cardinalities. Taking cardinalities of F gives precisely Nat.card P_N=∏_{p∈N.primeFactors}Nat.card P_(p^(N.factorization p)).

## Key steps

1. Verify the row-scaling equivalence relation and finiteness for nonzero moduli.
2. Handle N=1 as a singleton quotient and empty product.
3. Factor N into pairwise coprime prime powers.
4. Construct the CRT ring isomorphism.
5. Transport unimodularity witnesses and units componentwise.
6. Prove the induced map of row-class quotients bijective and take finite cardinalities.

## Reference use

### local-project

Queries:
- `dedekindPsi|ProjectiveLine|unimodularRow|Gamma0`
- `card.*ProjectiveLine|ProjectiveLine.*card|Gamma0.*(index|card)|(index|card).*Gamma0|dedekindPsi`
- `chineseRemainder|primeFactors|factorization|isUnit_iff|isUnit.*coprime`
- `prod_pow_primeFactors|prod.*factorization|factorization.*prod|squarefree_iff|Squarefree.*factorization`
- `rg -n 'p10_17ae7b7d_idx_(coset_row_card|prime_power_row_card|crt_row_card|dedekind_psi_product)' .humanize --glob 'dag.json' --glob 'parent-child-handoff.json'`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o TargetAbsence.olean TargetAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o ChildTypes.olean ChildTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-coset-index-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Factorization/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Nat/Squarefree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/index-split-ssqaob6l/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/index-split-ssqaob6l/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/index-split-ssqaob6l/report.json`

The snapshot matches project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Both tracked snapshot trees and all nine pinned dependency checkouts were clean. The sources supply the squarefree-divisor definition of dedekindPsi, Chinese remaindering, the prime-power unit criterion, prime factorization, and the left-coset convention. No matching coset-index or projective-row cardinality theorem was found. The projective-line module is outside the frozen imports, so the proposed types express its mathematical quotient explicitly using Quot. No proposed name occurred in local DAGs or frozen handoffs. All four exact types compiled after import Submission; reflexivity checks confirmed the left-coset quotient, scalar unit multiplication, and special-linear matrix multiplication. The types and checked library declarations have only propext, Classical.choice and Quot.sound as transitive axioms. The matching policy digest was 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96. Only listed lines 10–12 were omitted in the disposable compiler copy; Lean confirmed all 56 targets absent. The receipt records exact omitted text, reversible reconstruction, original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and build hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539. Original contracts and handoffs were unchanged. These are interface diagnostics, not comparator acceptance of theorem proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
