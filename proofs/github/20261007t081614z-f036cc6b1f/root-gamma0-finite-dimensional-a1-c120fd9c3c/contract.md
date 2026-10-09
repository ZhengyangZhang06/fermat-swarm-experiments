<!-- theorem-id: fermat-p01/root.gamma0_finite_dimensional-a1 -->

## Theorem `Submission.f036cc6b1f_finite_dimensional`

For every natural number M with M ≠ 0, the complex vector space CuspForm (CongruenceSubgroup.Gamma0 M) 2 is finite-dimensional.

Node: `root.gamma0_finite_dimensional-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/40, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/41, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/42

## Lean problem

Declaration: `Submission.f036cc6b1f_finite_dimensional`

```lean
∀ (M : ℕ) [NeZero M], FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)
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

- Parent DAG node: `root`
- Child DAG node: `root.gamma0_finite_dimensional-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix M ∈ ℕ with M ≠ 0, put Γ = Γ₀(M), and write V = S₂(Γ). Identify Γ with its standard image acting on the upper half-plane. The principal congruence group Γ(M), the kernel of reduction SL₂(ℤ) → SL₂(ℤ/Mℤ), is normal and has finite index because its target is finite. It is contained in Γ, so Γ has finite index d ≥ 1. These facts also appear in the pinned CongruenceSubgroups.lean, including CongruenceSubgroup.instFiniteIndexGamma0. The translation T = ((1,1),(0,1)) belongs to Γ, and T^M belongs to Γ(M).
2. Every rational boundary point σ∞, with σ ∈ SL₂(ℤ), is a cusp of Γ: normality gives σT^Mσ⁻¹ ∈ Γ(M) ⊆ Γ, a nontrivial parabolic fixing σ∞. Conversely, a noncentral parabolic integer matrix has a rational fixed point or fixes infinity, as follows from its repeated-root fixed-point equation. Thus the cusp condition on f ∈ V applies to every integer-matrix translate f|₂σ. Such a translate is holomorphic, tends to zero at infinity, and is M-periodic, since σT^Mσ⁻¹ ∈ Γ. The original f is also 1-periodic.
3. We record the analytic facts used below. A holomorphic h-periodic function g, with h > 0, bounded at infinity descends under q = exp(2πiz/h) to a holomorphic function G on the punctured unit disk: different logarithms differ by integral multiples of h, and local logarithms prove holomorphy. Boundedness removes the singularity at zero. Taylor expansion therefore gives g(z) = Σₙ≥0 aₙ exp(2πinz/h), absolutely convergent at every point of the upper half-plane. The coefficients are unique and depend linearly on g. Their simultaneous vanishing implies g = 0. If the coefficients through degree b vanish, then G(q) = q^(b+1)H(q), where H is holomorphic and bounded on every smaller closed disk; hence |g(x+iy)| ≤ C exp(−2π(b+1)y/h) for sufficiently large y, uniformly in x. These are the cusp-function and q-expansion results of the pinned QExpansion.lean, including UpperHalfPlane.hasSum_qExpansion.
4. Choose representatives γ₁,…,γ_d for Γ\SL₂(ℤ), with γ₁ = I, and define N(f)(z) = ∏ᵢ(f|₂γᵢ)(z). This product is holomorphic. For s ∈ SL₂(ℤ), right multiplication permutes the cosets: γᵢs = δᵢγⱼ with δᵢ ∈ Γ. The slash composition identity and f|₂δᵢ = f therefore permute the factors. Since all these matrices have determinant one, the product of the weight-two automorphy factors is precisely the weight-2d automorphy factor. Consequently N(f) is invariant of weight 2d under SL₂(ℤ). Every factor is bounded at infinity by step 2, so N(f) is bounded there. Full-group invariance gives boundedness at every cusp. Thus N(f) is a level-one modular form of natural weight 2d.
5. If f ≠ 0, every factor f|₂γᵢ is nonzero, because slash by γᵢ⁻¹ is its inverse. Each factor has an M-periodic expansion from step 3. Its coefficient sequence is not identically zero, so it has a least degree mᵢ with nonzero coefficient. In the product of these finitely many absolutely convergent series, the coefficient at degree Σᵢmᵢ is the product of those nonzero coefficients: every other possible contribution contains a coefficient below one of the least degrees. That product is nonzero in ℂ. Uniqueness of Taylor expansion shows that N(f) is not identically zero.
6. Put b = floor(2d/12). Suppose the period-one coefficients aₙ(f) vanish for every 0 ≤ n ≤ b. Step 3 gives |f(x+iy)| ≤ C exp(−2π(b+1)y) for large y. The identity representative contributes exactly f to N(f), and all other factors are bounded at infinity. Therefore N(f) satisfies the same exponential upper bound, with a possibly larger constant.
7. Let G be the period-one disk function of N(f). The preceding bound gives |G(q)| ≤ C'|q|^(b+1) for sufficiently small nonzero q. Its coefficients through degree b vanish. Indeed, if m ≤ b were its least nonzero degree, Taylor expansion would give G(q)/q^m → a_m ≠ 0 along positive real q → 0, whereas the bound forces this quotient to tend to zero. The zero series already has the required vanishing. Hence the q-expansion order of N(f) is strictly greater than b.
8. Apply ModularForm.sturm_bound_levelOne_nat from the pinned LevelOne/DimensionFormula.lean to the level-one form N(f) of natural weight 2d. Its hypothesis is exactly that its q-expansion order exceeds floor(2d/12), established in step 7. It follows that N(f) = 0. Step 5 then implies f = 0.
9. Define the complex-linear map L : V → ℂ^(b+1) by L(f) = (a₀(f),…,a_b(f)); linearity follows from step 3. Step 8 shows that its kernel is zero, so L is injective. A vector space admitting an injective linear map into a finite-dimensional vector space is finite-dimensional: the map identifies it with a subspace of the codomain. Therefore V is finite-dimensional over ℂ, as claimed.

## Key steps

1. Establish finite index and normal principal-congruence containment.
2. Obtain periodic Fourier expansions, uniqueness, and vanishing-order decay.
3. Construct the finite coset product as a level-one modular form of weight twice the index.
4. Prove the product is nonzero when the original form is nonzero.
5. Transfer sufficiently many vanishing coefficients to the product and apply the level-one Sturm bound.
6. Deduce injectivity of a finite coefficient map and finite-dimensionality.

## Reference use

### local-project

Queries:
- `rg -n 'heckeTLin|InnerProductSpace.Core|iSup_iInf_eq_top_of_commute|sturm_bound_levelOne_nat' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb`
- `grep -RnE 'finiteDimensional|FiniteDimensional|InnerProductSpace.Core|heckeTLin.*commut|heckeTLin.*[Ss]ymmet'`
- `grep -nE 'Gamma0|FiniteIndex|Normal'`
- `grep -nE 'iSup_iInf_eq_top_of_commute|sturm_bound_levelOne_nat|hasSum_qExpansion|qExpansion_coeff_unique|instFiniteIndexGamma0|petersson_slash|structure InnerProductSpace.Core|eq_one_or_neg_one_of_mem_fdo_mem_fd'`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `#print axioms CuspForm.heckeTLin`
- `#print axioms ModularForm.heckeT_apply`
- `#print axioms CongruenceSubgroup.instFiniteIndexGamma0`
- `#print axioms UpperHalfPlane.hasSum_qExpansion`
- `#print axioms LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`
- `#print axioms ModularForm.sturm_bound_levelOne_nat`
- `#print axioms UpperHalfPlane.petersson_slash`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperator.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean`
- `/tmp/fermat_p01_decomposition_a90tkggj/CheckDependencyTypes.lean`
- `/tmp/fermat_p01_decomposition_a90tkggj/CheckDependencyTypes.log`
- `/tmp/fermat_p01_decomposition_a90tkggj/CheckLibrary.log`
- `/tmp/fermat_p01_decomposition_a90tkggj/Submission.log`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The installed mathlib has that revision and clean status; the compiled project dependency sources match the snapshot byte-for-byte. ripgrep is unavailable, so the attempted rg search was followed by grep and Python file inspection. The sources establish the exact Hecke normalization, finite index, Fourier expansion and uniqueness, level-one Sturm bound, Petersson covariance, invariant measure, InnerProductSpace.Core, and the arbitrary-family simultaneous-eigenspace theorem. No suitable Gamma0 finite-dimensionality or bundled Hecke symmetry/commutation theorem was found in the searched Definitions and mathlib modular-form directories. All seven audited declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. The three proposed types elaborate against the unchanged contract imports; an anonymous rfl check confirms that the inner-product instance induced from B has inner product B.inner. However, literal import Submission validation is blocked: unchanged Submission.lean fails at its attribute commands with unknown constants FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions and FreyPackage.ModMCarrier.coe_rescaleLin_apply. No project source was changed.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
