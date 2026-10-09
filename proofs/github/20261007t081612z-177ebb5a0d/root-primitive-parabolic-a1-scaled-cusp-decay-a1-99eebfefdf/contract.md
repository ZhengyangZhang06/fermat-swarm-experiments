<!-- theorem-id: fermat-p02/root.primitive_parabolic-a1.scaled_cusp_decay-a1 -->

## Theorem `Submission.p02_es_177ebb5a_pp_scaled_cusp_decay`

Let N,n be natural numbers with N≠0, let f be a cusp form for Γ₀(N) of weight n+2, and let σ∈SL₂(ℤ). Define j(σ,τ)=σ₂₁τ+σ₂₂ and u(τ)=j(σ,τ)^{−(n+2)}f(στ). There exist real numbers a,C,Y with a>0 and C≥0 such that ‖u(τ)‖≤C exp(−a Im τ) whenever τ∈ℍ and Y≤Im τ.

Node: `root.primitive_parabolic-a1.scaled_cusp_decay-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/27

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_pp_scaled_cusp_decay`

```lean
∀ (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ), ∃ (a C Y : ℝ), 0 < a ∧ 0 ≤ C ∧ ∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖(HeckeEis.jFactor σ τ) ^ (-((n : ℤ) + 2)) * f (σ • τ)‖ ≤ C * Real.exp (-a * τ.im)
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

- Parent DAG node: `root.primitive_parabolic-a1`
- Child DAG node: `root.primitive_parabolic-a1.scaled_cusp_decay-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N,n,f,σ as in the statement. Put k=n+2 and u(z)=j(σ,z)^(−k)f(σz). The matrix σ acts holomorphically on ℍ, its denominator j(σ,z) is nonzero there, and f is holomorphic by the cusp-form hypothesis. Therefore u is holomorphic on ℍ.
2. Write T=(1 1;0 1). The subgroup Γ(N) is the kernel of reduction modulo N, hence is normal in SL₂(ℤ). The matrix T^N=(1 N;0 1) belongs to Γ(N), and every element of Γ(N) belongs to Γ₀(N), since its lower-left entry is zero modulo N. Consequently η=σT^Nσ⁻¹ belongs to Γ₀(N).
3. For determinant-one matrices α,β, direct multiplication gives j(αβ,z)=j(α,βz)j(β,z). Since σT^N=ησ and j(T^N,z)=1, this gives j(σ,z+N)=j(η,σz)j(σ,z). Modularity of f gives f(σ(z+N))=f(ησz)=j(η,σz)^k f(σz). Substitution in u and cancellation of the nonzero factors prove u(z+N)=u(z). Iterating this identity in both directions proves invariance under every integer multiple of N.
4. Since N≠0, N>0. The matrix T^N is noncentral parabolic and fixes infinity; conjugation shows that η is noncentral parabolic and fixes c=σ∞. Together with η∈Γ₀(N), this proves that c is a cusp in the frozen cusp-form definition. That definition, applied to the scaling matrix σ, says that the weight-k slash of f by σ tends to zero at imaginary infinity. The SL slash formula identifies this slash with u. Thus, for every ε>0, some height Yε satisfies |u(x+iy)|<ε for every real x and every y≥Yε with y>0. This is uniform in x.
5. Set a=2π/N>0 and q(z)=exp(2πiz/N). This map sends ℍ onto the punctured unit disk. Two points have the same q-value exactly when they differ by an integer multiple of N: equality of the moduli forces equal imaginary parts, and equality of the arguments makes the real difference an integer multiple of N. Periodicity therefore defines a single-valued function U on that disk by U(q(z))=u(z). Near every nonzero q-value, a local branch of the logarithm gives a holomorphic inverse z=N log(q)/(2πi), so U is holomorphic.
6. The equality |q(z)|=exp(−a Im z) and the uniform vanishing in step 4 imply U(q)→0 as q→0. The removable-singularity theorem extends U holomorphically to zero with U(0)=0. Its convergent power series near zero has zero constant coefficient. Factoring that series gives U(q)=qV(q), with V holomorphic near zero. Choose 0<r<1 whose closed disk lies in this neighborhood. Continuity on this compact disk supplies a finite bound M≥0 for |V| there. Put C=max(1,M), so C≥0.
7. Choose Y=max(1,log(1/r)/a). If Im τ≥Y, then |q(τ)|=exp(−a Im τ)≤r. Hence |u(τ)|=|U(q(τ))|≤C|q(τ)|=C exp(−a Im τ), proving the exact assertion. Steps 5–6 are also the analytic conclusion packaged by UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty in the pinned Mathlib/NumberTheory/ModularForms/QExpansion.lean; steps 1–4 establish its holomorphy, positive-period, vanishing, and consequent boundedness hypotheses.

## Key steps

1. Establish holomorphy of the scaled function using the nonvanishing denominator.
2. Use normality of Γ(N) to place σT^Nσ⁻¹ in Γ₀(N).
3. Combine modularity and the automorphy-factor identity to obtain period N.
4. Identify σ∞ as a cusp and obtain uniform vanishing at imaginary infinity.
5. Descend through q=exp(2πiz/N), remove the singularity at zero, and factor out q.
6. Bound the remaining holomorphic factor and choose the required constants.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|IsEquivariantPrimitiveWith|IsParabolicCocycle|eichlerShimuraMap_injective|exp_decay_atImInfty`
- `isCusp|isZeroAt|zero_at|conj|slash|normal|strictPeriods`
- `trace.*(sq|\^ 2)|parabolic.*conjug|conjug.*parabolic|exists.*(T \^|T\^)`
- `coe_T_zpow|T_zpow|neg.*smul|smul.*neg|def ofComplex|ofComplex_apply`
- `rg -n 'p02_es_177ebb5a_pp_(scaled_cusp_decay|primitive_cusp_limit|integral_parabolic_normal_form)' Submission.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes`
- `git -C .lake/packages/mathlib status --short`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `cmp Definitions/Def_HeckeEis_EichlerIntegral.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `cmp Definitions/Def_HeckeEis_BinaryFormRep.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `cmp Definitions/Def_Gamma0CoeffCohomology.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_177ebb5a_pp_typecheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/tmp/p02_177ebb5a_pp_typecheck.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The installed mathlib matches that revision and has clean Git status; the three relevant project definition files match the snapshot byte-for-byte. Existing infrastructure supplies sub_eq_cocycle, binaryFormRepSL_linePow, jFactor_ne_zero, Gamma_normal, ModularGroup_T_pow_mem_Gamma, and cusp vanishing after slash. QExpansion.lean supplies exponential decay from positive periodicity, holomorphy, boundedness, and vanishing at imaginary infinity. The searched matrix, modular-form, and project-definition sources contain no matching integral conjugacy theorem covering every trace-squared-four matrix. The proposed identifiers have no matches in Submission or the DAG metadata. All three exact propositions elaborate after import Submission under Lean 4.33.1; additional checked equalities verify matrix multiplication and matrix negation for the inferred special-linear-group instances. Transitive axiom checks for the seven inspected reusable lemmas report only propext, Classical.choice, and Quot.sound. These checks validate the interfaces and reference reuse, not acceptance of new theorem proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/160

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
