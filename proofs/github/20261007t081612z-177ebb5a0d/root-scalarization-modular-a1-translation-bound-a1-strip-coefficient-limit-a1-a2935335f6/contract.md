<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1 -->

## Theorem `Submission.p02_es_177ebb5a_tb_strip_coefficient_limit`

Let n∈ℕ, let u:ℍ→ℂ be continuous, and let G:ℍ→BinaryForm ℂ n satisfy IsEichlerIntegral n u G. Let a,C,Y,L∈ℝ satisfy a>0, C≥0, and L≥0. Assume |u(τ)|≤C exp(−a Im τ) whenever Im τ≥Y. Then there exist A∈BinaryForm ℂ n and K≥0 such that, for every τ with 0≤Re τ≤L and Im τ≥max(1,Y), every monomial coefficient of G(τ)−A has absolute value at most K(1+Im τ)^n exp(−a Im τ).

Node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/48

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/126, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/127, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/128

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_tb_strip_coefficient_limit`

```lean
∀ (n : ℕ) (u : UpperHalfPlane → ℂ) (G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (a C Y L : ℝ), 0 < a → 0 ≤ C → 0 ≤ L → Continuous u → HeckeEis.IsEichlerIntegral n u G → (∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖u τ‖ ≤ C * Real.exp (-a * τ.im)) → ∃ (A : ↥(HeckeEis.BinaryForm ℂ n)) (K : ℝ), 0 ≤ K ∧ ∀ τ : UpperHalfPlane, 0 ≤ τ.re → τ.re ≤ L → max 1 Y ≤ τ.im → ∀ d : Fin 2 →₀ ℕ, ‖MvPolynomial.coeff d ((G τ).val - A.val)‖ ≤ K * (1 + τ.im) ^ n * Real.exp (-a * τ.im)
```

### Frozen project context

`Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean` at `1f74c284b125d4c45f527f2d621597fcf1e103a9` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HeckeEis_eichlerShimuraMap_injective.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_injective (N : ℕ) [NeZero N] (n : ℕ) :
    Function.Injective
      (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f) := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put y₀=max(1,Y). Every homogeneous binary form R of degree n has a unique expansion R=Σ_{r=0}^n R_r X^rY^(n−r). Indeed, every exponent pair in its support has sum n, and therefore is uniquely (r,n−r). Define ‖R‖c=max_{0≤r≤n}|R_r|. The coordinate map identifies this space isometrically with the finite product ℂ^(n+1) equipped with its maximum norm, which is complete. Coefficients of monomials whose total degree differs from n vanish.
2. On the open upper half-plane, the defining derivative condition says that the derivative of the r-th coefficient of G is u(z) binom(n,r) z^r. These derivatives are continuous because u is continuous and z↦z^r is continuous. Restricting to horizontal or vertical segments contained in ℍ therefore permits the real fundamental theorem of calculus, with the vertical derivative multiplied by i.
3. For 0≤x≤L and t≥y₀, |x+it|≤L+t≤(L+1)(1+t). The last quantity is at least 1. Since r≤n and binom(n,r)≤2^n, every derivative coefficient has absolute value at most D(1+t)^n exp(−at), where D=C·2^n·(L+1)^n≥0. Thus the same bound holds for the maximum coefficient norm of the derivative.
4. Define J=∫₀^∞(1+s)^n exp(−as) ds. This is finite and nonnegative. For s≥0, (1+s)^n≤2^n(1+s^n). The nonnegative terms of the exponential series imply s^n≤n!(2/a)^n exp(as/2). Consequently the integrand is at most 2^n(1+n!(2/a)^n)exp(−as/2), an integrable function with integral 2^(n+1)(1+n!(2/a)^n)/a. These inequalities also hold for n=0.
5. Fix x∈[0,L] and t≥y≥y₀. Integrate each coefficient along the vertical segment and use the derivative bound and |i|=1. Taking the maximum over the finitely many coefficients gives ‖G(x+it)−G(x+iy)‖c≤D∫_y^t(1+s)^n exp(−as) ds. Substitute s=y+v. Since y,v≥0, 1+y+v≤(1+y)(1+v), so this is at most DJ(1+y)^n exp(−ay).
6. The factor (1+y)^n exp(−ay) tends to zero. For y≥1, it is at most 2^n y^n exp(−ay), while the exponential series gives exp(ay)≥(ay)^(n+1)/(n+1)!. Thus it is at most 2^n(n+1)!/(a^(n+1)y), which tends to zero. For any two sufficiently large heights, order them and apply step 5; its right side is then arbitrarily small. Hence G(x+iy) is Cauchy as y→∞. Completeness supplies a limit A_x in the homogeneous binary-form space. Passing t→∞ in step 5, using continuity of the norm, yields ‖G(x+iy)−A_x‖c≤DJ(1+y)^n exp(−ay).
7. Horizontal integration at height y≥y₀ gives ‖G(x+iy)−G(iy)‖c≤xD(1+y)^n exp(−ay). The bound tends to zero by step 6. Taking limits of both terms shows ‖A_x−A_0‖c=0, hence A_x=A_0, for every x∈[0,L]. This includes the case L=0.
8. Set A=A_0 and K=DJ. Both D and J are nonnegative, so K≥0. For any τ in the stated strip, write τ=x+iy and apply step 6 with A_x=A. Every degree-n coefficient of G(τ)−A is bounded by its maximum coefficient norm, giving the required estimate. Every other coefficient is zero by homogeneity, and the right side is nonnegative. This proves the estimate for every exponent d and completes the statement.

## Key steps

1. Identify homogeneous binary forms with the complete finite space of degree-n coefficients.
2. Bound all coefficient derivatives uniformly by a polynomial times an exponential on the strip.
3. Prove integrability of the polynomial-exponential majorant.
4. Integrate vertically to obtain a uniform tail estimate and coefficient limits.
5. Integrate horizontally to show that all vertical limits coincide.
6. Use the common limit and vanishing off-degree coefficients to obtain the stated bound.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|isBoundedAtImInfty_iff|binaryFormRepSL|eichlerShimuraMap_injective`
- `theorem.*(T_pow|T_zpow)|def T|lemma.*(T_pow|T_zpow)|coe_T|T_smul`
- `integrable.*exp|exp.*integrable`
- `eq_C_of.*comp|comp.*eq_C|periodic|Periodic`
- `norm_eval|eval.*norm|norm.*eval`
- `rg -n --hidden -g 'dag.json' -g 'decomposition-v*.json' -g '*.lean' 'p02_es_177ebb5a_tb_(strip_coefficient_limit|fixed_form|eval_bound|periodic_strip_bound)' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_tb_decomposition_types.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/Polynomial`
- `/tmp/p02_tb_decomposition_types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected project definitions match the local elaboration environment; local mathlib has the pinned revision and clean Git status. IsEichlerIntegral is coefficientwise differentiation, and binaryFormRepSL uses column substitution, so T^N substitutes (X,Y) ↦ (X,NX+Y). Mathlib supplies homogeneous support and evaluation formulas, exponential decay and integrability, translation action formulas, and the exact eventual-bound criterion. The polynomial searches found no relevant translation-fixed classification; the evaluation searches found no matching homogeneous coefficient-bound estimate. All four proposed types elaborate after import Submission. The proposed names have no match in the current DAG or recorded decompositions. Transitive axiom checks for binaryFormRepSL_apply_coe, modular_T_zpow_smul, isBoundedAtImInfty_iff, and tendsto_pow_mul_exp_neg_atTop_nhds_zero report only propext, Classical.choice, and Quot.sound. These checks validate interfaces and library evidence, not acceptance of the proposed child proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/582

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
