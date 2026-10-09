<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1.bezout_exceptional_lift-a1 -->

## Theorem `Submission.f036cc6b1f_pc_hi_gpt_bezout_lift`

Let M be a nonzero natural number and p a natural prime with p not dividing M. Let Γ = Γ₀(M), let ι : SL₂(ℤ) → GL₂(ℝ) be the canonical embedding, let α = ModularForm.heckeMatrix p 0, and let C = ModularForm.heckeDiagMatrix p. There exist an integer v and matrices σ, β in SL₂(ℤ) such that p does not divide v, both σ and β belong to Γ, the first row of σ is (p, −v), and α·ι(σ) = ι(β)·C.

Node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1.bezout_exceptional_lift-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/205

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_hi_gpt_bezout_lift`

```lean
∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → ¬ p ∣ M → ∃ (v : ℤ) (σ β : Matrix.SpecialLinearGroup (Fin 2) ℤ), (¬ (p : ℤ) ∣ v) ∧ σ ∈ CongruenceSubgroup.Gamma0 M ∧ β ∈ CongruenceSubgroup.Gamma0 M ∧ σ 0 0 = (p : ℤ) ∧ σ 0 1 = -v ∧ ModularForm.heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ σ = Matrix.SpecialLinearGroup.mapGL ℝ β * ModularForm.heckeDiagMatrix p
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

- Parent DAG node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1.bezout_exceptional_lift-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix M and p satisfying the hypotheses. Primality gives p ≥ 2. Since p does not divide M, gcd(p,M) = 1: this gcd divides p, so it is either 1 or p, and the latter alternative would imply p divides M.
2. Apply the integer Bézout identity for natural inputs, Nat.gcd_eq_gcd_ab. Taking u = Nat.gcdA p M and v = Nat.gcdB p M gives the integer equality p·u + M·v = 1.
3. The integer p does not divide v. Indeed, if it divided v, it would divide both p·u and M·v, hence their sum 1 by step 2. This is impossible because p ≥ 2.
4. Define integer matrices σ = ((p, −v), (M, u)) and β = ((1, −v), (M, p·u)). Their determinants are respectively p·u − (−v)·M = p·u + M·v = 1 and 1·(p·u) − (−v)·M = p·u + M·v = 1. They therefore define elements of SL₂(ℤ). Their displayed entries give σ₀₀ = p and σ₀₁ = −v.
5. Both matrices have lower-left entry M. This entry reduces to zero modulo M, so the defining membership criterion for Γ₀(M) shows σ ∈ Γ and β ∈ Γ.
6. Since p ≠ 0, the pinned Hecke definitions give α = diag(1,p) and C = diag(p,1). The canonical embedding ι casts each integer matrix entry to the reals. Direct matrix multiplication gives α·ι(σ) = ((p, −v), (p·M, p·u)) and ι(β)·C = ((p, −v), (M·p, p·u)). These real matrices are equal because p·M = M·p. Equality of their underlying matrices gives equality in GL₂(ℝ).
7. The witnesses v, σ, β satisfy the nondivisibility condition from step 3, both membership conditions from step 5, the first-row conditions from step 4, and the required Hecke identity from step 6. This proves the full existential conclusion.

## Key steps

1. Deduce coprimality of p and M and obtain integer Bézout coefficients.
2. Use the Bézout identity to prove that p does not divide v.
3. Construct σ and β explicitly and verify both determinants are one.
4. Check Gamma0 membership through the lower-left entries.
5. Compute both embedded matrix products using the nonzero-p Hecke definitions.

## Reference use

### local-project

Queries:
- `def heckeMatrix|def heckeDiagMatrix|heckeMatrix.*coe|coe.*heckeMatrix|heckeDiagMatrix.*coe|coe.*heckeDiagMatrix|exists.*[Bb]ezout|transversal`
- `mapGL|coe_inv|coe_mul|det_coe|det_eq|def mk|fin_two`
- `intCast_zmod_eq_zero|val_lt|val_injective|intCast_zmod_cast|cast_val`
- `transversal|[Bb]ezout.*hecke|hecke.*[Bb]ezout|projective.*index`
- `f036cc6b1f_pc_hi_gpt_(unique_projective_index|bezout_lift)`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/f036cc6b1f_gpt_split_23h6rj5x/Types.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperator.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Data/Int/GCD.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Data/Nat/Prime/Defs.lean`
- `/tmp/f036cc6b1f_gpt_split_23h6rj5x/Types.lean`
- `/tmp/f036cc6b1f_gpt_split_23h6rj5x/Types.log`
- `/tmp/f036cc6b1f_gpt_split_23h6rj5x/Compatibility.json`
- `/tmp/f036cc6b1f_gpt_split_23h6rj5x/check-command.json`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected sources supply the exact Hecke matrix values, Gamma0 membership criterion, SL2 inverse formula, canonical real embedding, Bézout identity, and residue/divisibility and representative lemmas. The project search found no matching transversal or Bézout–Hecke helper; neither proposed identifier occurs in the searched DAG metadata. Both literal child propositions elaborated successfully after import Submission. Fully explicit elaboration confirmed Units.instMul over Matrix.semiring and the canonical integer-to-real algebra instance. Installed mathlib is clean at the pinned revision, and all 20 imported project sources in the selected offline cache match the snapshot. Transitive axiom checks of the cited supporting declarations returned only subsets of propext, Classical.choice, and Quot.sound. These checks validate the proposed interfaces and library references; they do not constitute comparator acceptance of child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/249

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
