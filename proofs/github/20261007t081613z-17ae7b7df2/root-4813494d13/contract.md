<!-- theorem-id: fermat-p10/root -->

## Theorem `CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero`

Prove `CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero` for `fermat-p10` using the exact frozen contract in `Fermat/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean`. Write the Lean solution in Submission.lean. Use the issue/PR workflow: complete and independently review the natural-language proof, publish every new named helper as an issue, and require the controller comparator and independent review before a solution PR is merged and its issue closed. Workers independently poll issues; do not dispatch or notify other workers. No web search. Do not import the original upstream solution of this target. Pinned unchanged libraries may be reused with exact provenance and axiom checks.

Node: `root`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: None (root)

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/372, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/374, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/375, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/376

## Lean problem

Declaration: `CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero`

```lean
∀ (N : ℕ) [NeZero N] (hg : ModularCurve.genusFormula N = 0) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), f = 0
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

# Final proof of the genus-zero weight-two cusp-form theorem

The declaration proved in `Submission.lean` is exactly

```lean
theorem CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero (N : ℕ) [NeZero N]
    (hg : ModularCurve.genusFormula N = 0) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f = 0
```

This handoff explains the actual root argument. It instantiates the accepted norm-vanishing and level-one valence theorems and then combines their inequalities with the defining genus equality. All the analytic and arithmetic dependency proofs remain in the integrated `Submission.lean`; they are existing accepted declarations, not additional assumptions or new helpers introduced by this root.

## Assumptions, notation and dependencies

Fix a natural number `N` with the supplied instance `NeZero N`, so `N ≠ 0`. Assume `hg : ModularCurve.genusFormula N = 0`, and let `f` be a weight-two cusp form for `CongruenceSubgroup.Gamma0 N`. Equality in the conclusion is equality of bundled cusp forms.

Write

\[
\mu=\operatorname{dedekindPsi}(N),\qquad
c=\operatorname{cuspCount}(N),\qquad
e_2=\operatorname{nuTwo}(N),\qquad
e_3=\operatorname{nuThree}(N),\qquad
\rho=(-1+\sqrt3\,i)/2.
\]

The four numerical quantities are natural numbers. Let `H = {z : ℂ | 0 < z.im}`. Every order used below is exactly the natural number `analyticOrderNatAt` appearing in the accepted dependency interfaces, with its displayed function and point; the root does not change the order convention or require a new assertion about finiteness.

The two directly invoked dependencies have the following complete hypotheses and conclusions.

1. `Submission.p10_17ae7b7d_gamma0_norm_vanishing`: for every natural `N`, with `NeZero N`, and every `f : CuspForm (CongruenceSubgroup.Gamma0 N) 2`, if `f ≠ 0`, there exist total functions `F A : ℂ → ℂ` such that:
   - `F` is complex differentiable on `H`;
   - some `z ∈ H` satisfies `F z ≠ 0`;
   - for every `z ∈ H`, `F (z + 1) = F z`;
   - for every `z ∈ H`, `F (-1 / z) = z ^ (2 * μ) * F z`;
   - `A` is complex analytic at zero;
   - there is a real `Y` such that every `z ∈ H` with `Y ≤ z.im` satisfies `F z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))`;
   - `c ≤ analyticOrderNatAt A 0`;
   - `e₂ ≤ analyticOrderNatAt F Complex.I`;
   - `2 * e₃ ≤ analyticOrderNatAt F ρ`.

2. `Submission.p10_17ae7b7d_level_one_valence_inequality`: for every natural `k` and every `F A : ℂ → ℂ`, assume `Even k`, complex differentiability of `F` on `H`, a nonzero value of `F` in `H`, the two transformation equations `F (z + 1) = F z` and `F (-1 / z) = z ^ k * F z` for all `z ∈ H`, analyticity of `A` at zero, and existence of a real `Y` giving the same eventual exponential expansion as above. Then, in the real numbers,

   \[
   \operatorname{analyticOrderNatAt}(A,0)
   +\frac{\operatorname{analyticOrderNatAt}(F,i)}2
   +\frac{\operatorname{analyticOrderNatAt}(F,\rho)}3
   \le \frac{k}{12}.
   \]

In particular, neither theorem assumes `genusFormula N = 0`, and neither invokes the root conclusion. The root supplies every hypothesis of the second theorem from the first, except parity, which follows from the explicit factor two.

## Numbered proof matching the Lean term

1. Argue by contradiction and assume `hf : f ≠ 0`. Apply `Submission.p10_17ae7b7d_gamma0_norm_vanishing N f hf`. Obtain `F`, `A`, their differentiability, nonzero-value, transformation and expansion properties, and the three natural-number order inequalities above. This is the `obtain` step of the Lean proof; the original `NeZero N` instance is passed unchanged.

2. Set `k = 2 * μ`. The library theorem `even_two_mul μ` proves `Even k`. Apply `Submission.p10_17ae7b7d_level_one_valence_inequality` with exactly this `k` and the functions and hypotheses from step 1. Put

   \[
   a=\operatorname{analyticOrderNatAt}(A,0),\quad
   b=\operatorname{analyticOrderNatAt}(F,i),\quad
   d=\operatorname{analyticOrderNatAt}(F,\rho).
   \]

   Interpreting these natural numbers in `ℝ`, the resulting inequality is

   \[
   a+b/2+d/3\le (2\mu)/12=\mu/6. \tag{1}
   \]

3. Cast the three order bounds from `ℕ` to `ℝ`. The natural-number cast preserves order and multiplication, so they become

   \[
   c\le a,\qquad e_2\le b,\qquad 2e_3\le d. \tag{2}
   \]

   These are exactly the three `exact_mod_cast` steps. Because 2 and 3 are positive, (2) gives

   \[
   c+e_2/2+2e_3/3\le a+b/2+d/3. \tag{3}
   \]

4. By its pinned definition, `ModularCurve.genusFormula N` is the rational number

   \[
   1+\mu/12-e_2/4-e_3/3-c/2.
   \]

   Apply the function `fun q : ℚ => (q : ℝ)` to `hg` using `congrArg`. Unfolding `ModularCurve.genusFormula` and simplifying the rational casts gives the real equality

   \[
   1+\mu/12-e_2/4-e_3/3-c/2=0. \tag{4}
   \]

   Multiplying (4) by two and rearranging gives

   \[
   c+e_2/2+2e_3/3=2+\mu/6. \tag{5}
   \]

5. Combining (1), (3), and (5) yields `2 + μ/6 ≤ μ/6`, and hence `2 ≤ 0` in `ℝ`, a contradiction. In Lean, `norm_num only [Nat.cast_mul, Nat.cast_ofNat]` puts the right side of the valence inequality into the real arithmetic form used here; `linarith only [hval, hc_real, h₂_real, h₃_real, hg_real]` checks this linear contradiction. Therefore `f = 0`. No further property of `f` or `N` is assumed.

## Dependency history and actual use

The selected root contract also preserves `Submission.p10_17ae7b7d_gamma0_coset_counts` and `Submission.p10_17ae7b7d_periodic_disk_extension`. The root does not call them directly. The retained proof of `gamma0_norm_vanishing` uses them: the first gives finite cosets and the numerical index, elliptic fixed-point and cusp-orbit counts, while the second supplies the analytic disk extension for periodic functions. The other previously accepted descendant declarations remain present with their original globally qualified names and types.

The accepted natural proof, `nodes/root/natural-proof-v140.md` in run `20261007T081613Z-17ae7b7df2`, supplies the detailed arithmetic, analytic norm and contour arguments behind those dependencies. Its steps 19, 20 and 28 correspond to the two direct applications and the final contradiction here; steps 1 and 28 supply the genus arithmetic. That reviewed document and the original scaffold remain unchanged. Speculative interfaces in the older scaffold are historical and are not additional premises of this implementation.

Integration removed a repeated block of 15 already present child declarations whose theorem bodies were identical to their retained copies. It also moved the exact root declaration from its earlier placeholder to its proof after the dependencies. No accepted child was renamed or replaced, and no new named helper was introduced.

## Library-reuse provenance and reference use

`reference_use` has exactly one source: **local-project**.

The local reference snapshot is
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f`.
Its `manifest.json` pins project commit `a97febc53b1c4d489edc54ca44132af7a21279b3` and mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. The following paths are relative to that snapshot; both Git revisions and clean statuses were inspected.

- `project/Definitions/Def_ModularCurve_GenusNumerics.lean:9–22` defines `nuTwo`, `nuThree`, `cuspCount`, and the exact rational `genusFormula` unfolded in step 4. `project/Definitions/Def_ModularCurve_X0.lean:201` defines the natural number `dedekindPsi`. Query: `rg -n 'genusFormula|nuTwo|nuThree|cuspCount|dedekindPsi' project/Definitions/Def_ModularCurve_GenusNumerics.lean project/Definitions/Def_ModularCurve_X0.lean`.
- `mathlib/Mathlib/Algebra/Ring/Parity.lean:95` proves `even_two_mul` by the witness expressing twice a number as its sum with itself. This discharges precisely the parity hypothesis in step 2.
- `mathlib/Mathlib/Data/Nat/Cast/Order/Basic.lean:70` gives `Nat.cast_le`; the standard cast simplification rules used by `exact_mod_cast` transport (2). `mathlib/Mathlib/Data/Nat/Cast/Basic.lean:56` gives `Nat.cast_mul`; it and the standard `Nat.cast_ofNat` rule normalize the valence weight. These are existing library facts, not new helpers.
- `mathlib/Mathlib/Data/Rat/Cast/CharZero.lean:42–63` supplies the cast rules for addition, subtraction, multiplication and division that simplify the image of (4). `congrArg` is Lean's ordinary equality congruence rule. Query for the preceding three files and `mathlib/Mathlib/Data/Rat/Cast/Defs.lean`: `rg -n 'even_two_mul|theorem cast_(mul|le|div|sub|add)|lemma cast_(mul|le|div|sub|add)' ...`.
- Query: `rg -n -i '\bvalence\b|weight_two_eq_zero|genusFormula' mathlib/Mathlib/NumberTheory/ModularForms`. It returned **no matches**. The argument therefore uses the accepted project dependency for valence; it does not claim a pre-existing mathlib solution to the root.

The imports remain the frozen `Mathlib` and `Definitions.Def_ModularCurve_GenusNumerics`. The package pins mathlib to the manifest revision and uses Lean 4.33.1; the reference mathlib checkout declares 4.33.0, so source inspection alone is not a compatibility certificate. The configured comparator must establish compatibility, exact frozen statement/context agreement, kernel replay and permitted transitive axioms on the committed candidate. The permitted foundational axioms are `propext`, `Quot.sound` and `Classical.choice`; no additional axiom is introduced here.

The original Submission header, contract and reviewed records are unchanged. Operator policy digest `96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96` permits only its listed negative attribute directives, lines 10–12 for this source commit and contract, to be omitted in private compiler copies after target-absence checks. That build-input policy is not a mathematical premise or proof-acceptance claim. Independent publication proof review and the final controller acceptance remain separate from this author handoff.

## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
