<!-- theorem-id: fermat-p01/root.gamma0_finite_dimensional-a1.coeff_vanishing_iff_decay-a1 -->

## Theorem `Submission.f036cc6b1f_fd_coeff_decay`

Let Γ be a subgroup of GL₂(ℝ), let k be an integer, and let f be a modular form of weight k for Γ. Assume 1 belongs to Γ.strictPeriods. For every natural number b, the period-one q-expansion coefficients of f vanish at every degree n ≤ b if and only if there exist real numbers C ≥ 0 and Y such that, for every z in the upper half-plane with Y ≤ Im z, ‖f(z)‖ ≤ C exp(−2π(b+1) Im z).

Node: `root.gamma0_finite_dimensional-a1.coeff_vanishing_iff_decay-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/23

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_fd_coeff_decay`

```lean
∀ (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) (k : ℤ) (f : ModularForm Γ k), (1 : ℝ) ∈ Γ.strictPeriods → ∀ b : ℕ, (∀ n : ℕ, n ≤ b → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) ↔ ∃ C Y : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, Y ≤ z.im → ‖f z‖ ≤ C * Real.exp (-2 * Real.pi * ((b + 1 : ℕ) : ℝ) * z.im)
```

### Frozen project context

`Fermat/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean` at `61b5f85556ac71631ccad822e0694511234f7132` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_finite_dimensional-a1`
- Child DAG node: `root.gamma0_finite_dimensional-a1.coeff_vanishing_iff_decay-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Γ, k, f, the strict-period hypothesis, and b. The positive strict period 1 makes infinity a cusp of Γ, by Subgroup.isCusp_of_mem_strictPeriods in the pinned Cusps.lean. Consequently f is holomorphic, is 1-periodic, and is bounded at infinity by its modular-form hypotheses.
2. Put q(z) = exp(2πiz) and F = UpperHalfPlane.cuspFunction 1 f. The pinned QExpansion.lean proves that F is holomorphic on the open unit disk, including zero, and that F(q(z)) = f(z). Its Taylor coefficient a_n at zero is exactly (UpperHalfPlane.qExpansion 1 f).coeff n. Its Taylor series converges throughout that disk. Also |q(z)| = exp(−2π Im z).
3. Suppose a_n = 0 for every n ≤ b. Removing these zero terms from the convergent Taylor series gives F(q) = q^(b+1) H(q), where H is holomorphic on the open unit disk: its power series is the shifted series with coefficients a_(n+b+1). On the compact disk |q| ≤ 1/2, continuity of H gives a bound |H(q)| ≤ C for some C ≥ 0.
4. Choose Y > 0 with exp(−2πY) ≤ 1/2. Whenever Im z ≥ Y, the preceding factorization and bound imply |f(z)| = |q(z)|^(b+1)|H(q(z))| ≤ C exp(−2π(b+1) Im z). This proves the forward implication, with constants satisfying the stated quantifiers.
5. Conversely, suppose the stated bound holds for C ≥ 0 and Y. If some coefficient of degree at most b were nonzero, choose the least such degree m. Then all coefficients of smaller degree vanish. Taylor expansion therefore writes F(q) = q^m H_m(q) near zero, with H_m holomorphic and H_m(0) = a_m ≠ 0.
6. For positive real t tending to zero, let z_t = i(−log t)/(2π). For sufficiently small t, this is in the upper half-plane and Im z_t ≥ Y; moreover q(z_t) = t. The assumed bound gives |F(t)/t^m| ≤ C t^(b+1−m). Since m ≤ b, the right side tends to zero. But F(t)/t^m = H_m(t) tends to a_m by continuity, forcing a_m = 0, a contradiction. Thus every coefficient through degree b vanishes, proving the reverse implication and the equivalence.

## Key steps

1. Use the positive strict period to obtain periodicity and boundedness at infinity.
2. Identify the q-expansion with the Taylor series of the holomorphic cusp function.
3. Factor out q^(b+1) and bound the remaining holomorphic function on a smaller closed disk.
4. Convert the disk estimate into a uniform exponential estimate.
5. For the converse, a least nonzero coefficient contradicts the estimate along positive real q tending to zero.

## Reference use

### local-project

Queries:
- `rg -n 'ModularForm.norm|norm_eq_zero_iff|sturm_bound_levelOne_nat|hasSum_qExpansion|instFiniteIndexGamma0' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb`
- `grep -R -n -E 'sturm_bound_levelOne_nat|hasSum_qExpansion|qExpansion_coeff_unique|instFiniteIndexGamma0|finiteDimensional|FiniteDimensional' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `grep -R -n -E 'isBigO.*norm|norm.*isBigO|coeff.*exp|exp.*coeff|order.*isBigO|isBigO.*order' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `#print axioms ModularForm.norm`
- `#print axioms ModularForm.norm_eq_zero_iff`
- `#print axioms ModularForm.sturm_bound_levelOne_nat`
- `#print axioms UpperHalfPlane.hasSum_qExpansion`
- `#print axioms CongruenceSubgroup.instFiniteIndexGamma0`
- `#print axioms FiniteDimensional.of_injective`
- `#print axioms ModularFormClass.analyticAt_cuspFunction_zero`
- `#print axioms ModularForm.qExpansion_add`
- `#print axioms ModularForm.qExpansion_smul`
- `#print axioms ModularFormClass.modularForm`
- `Python scan of dag.json and nodes/**/*.json for f036cc6b1f_fd_coeff_decay, f036cc6b1f_fd_norm_bound, and f036cc6b1f_fd_sturm`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-gamma0-finite-dimensional-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/NormTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/GroupTheory/Index.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/Submission.lean`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckDependencyTypes.lean`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckDependencyTypes.log`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckNormInstances.lean`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckNormInstances.log`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/Submission.log`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckSubmission.log`

The snapshot pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib has that revision and clean status; the inspected library files and all 20 compiled project dependencies match the snapshot byte-for-byte. The requested rg command was attempted, but rg is unavailable; grep and Python supplied the searches. NormTrace.lean already provides ModularForm.norm and ModularForm.norm_eq_zero_iff, eliminating separate construction and nonvanishing obligations. QExpansion.lean supplies the analytic disk function, convergent expansion, and coefficient linearity; DimensionFormula.lean supplies the exact level-one Sturm bound. No matching Gamma0 finite-dimensionality theorem or norm-domination theorem was found in the searched directories. All ten audited declarations use only propext, Classical.choice, and Quot.sound. The three proposed types elaborate under the actual Definitions.Def_ModularForm_HeckeOperatorForms import. Separate checks verify the norm's inferred finite-relative-index, determinant, and modular-form instances, its weight, and its defining finite product. No proposed identifier occurs in the active DAG or handoffs. However, literal import Submission validation is blocked: unchanged Submission.lean fails on unknown constants FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions and FreyPackage.ModMCarrier.coe_rescaleLin_apply. These proposed children must not activate until that required import gate passes. No proof acceptance is claimed.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
