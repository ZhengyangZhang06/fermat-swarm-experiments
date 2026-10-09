<!-- theorem-id: fermat-p02/root.scalarization_derivative-a1 -->

## Theorem `Submission.p02_es_177ebb5a_scalarization_derivative`

Let n∈ℕ, let h : ℍ → ℂ be holomorphic, expressed exactly by DifferentiableOn ℂ (h ∘ ofComplex) on {z : ℂ | 0 < z.im}, and let E : ℍ → BinaryForm ℂ n satisfy IsEichlerIntegral n h E. Define P(z)=E(ofComplex z)(1,−z) for z∈ℂ. Then, for every τ∈ℍ, its complex derivative of order n+1 satisfies P⁽ⁿ⁺¹⁾(τ)=(-1)^n n! h(τ).

Node: `root.scalarization_derivative-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/68, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/69

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_scalarization_derivative`

```lean
∀ (n : ℕ) (h : UpperHalfPlane → ℂ) (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), DifferentiableOn ℂ (fun z : ℂ => h (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} → HeckeEis.IsEichlerIntegral n h E → ∀ τ : UpperHalfPlane, iteratedDeriv (n + 1) (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z) (E (UpperHalfPlane.ofComplex z)).val) (τ : ℂ) = ((-1 : ℂ) ^ n * (Nat.factorial n : ℂ)) * h τ
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

- Parent DAG node: `root`
- Child DAG node: `root.scalarization_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Work on the open set U={z∈ℂ : Im z>0}. On U, ofComplex is the usual upper-half-plane identification. Write E(z)=Σ_{j=0}^n a_j(z)X^jY^{n-j}. The frozen IsEichlerIntegral predicate gives a complex derivative for every coefficient at every point of U and says coefficientwise that E′(z)=h(z)(zX+Y)^n. Thus all a_j are holomorphic on U. In particular all finite expressions below are holomorphic there.
2. For 0≤r≤n+1 define Q_r(z)=(∂_Y^r E(z))(1,−z), differentiating only the polynomial variable Y inside ∂_Y. Every term of E has Y-degree at most n, so Q_{n+1}=0. Differentiating the finite coefficient expression for Q_r, and separately differentiating the substituted value −z, gives for 0≤r≤n the identity Q_r′(z)=h(z)(∂_Y^r(zX+Y)^n)(1,−z)−Q_{r+1}(z). Coefficient differentiation commutes with ∂_Y because both operations act termwise on a fixed finite sum.
3. Repeated polynomial differentiation gives ∂_Y^r(zX+Y)^n=n!/(n−r)!·(zX+Y)^(n−r) for r≤n. When r<n the remaining exponent is positive, so evaluation at (1,−z) is zero. Therefore Q_r′=−Q_{r+1} for r<n. At r=n the evaluated polynomial is n!, and Q_{n+1}=0, so Q_n′=n!h. If n=0 this last identity already says Q_0′=h.
4. On U the scalar function P in the statement equals Q_0. Induction on r, using the recurrence in step 3, gives iteratedDeriv r P=(-1)^r Q_r on U for 0≤r≤n. In the induction step these functions agree on an open neighborhood of every point of U, so their derivatives agree there. The identity iteratedDeriv (r+1) P=deriv (iteratedDeriv r P) is iteratedDeriv_succ from Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean.
5. Differentiate the r=n identity once more and use Q_n′=n!h. This gives iteratedDeriv (n+1) P(z)=(-1)^n n!h(z) throughout U. Every τ∈ℍ lies in U, and all derivatives are local, so the definition of ofComplex outside U has no effect. Evaluating at τ proves exactly the displayed Lean conclusion, including n=0.

## Key steps

1. Interpret IsEichlerIntegral as coefficientwise differentiation on the open upper half-plane.
2. Define evaluated Y-partial derivatives Q_r.
3. Prove Q_r′=−Q_{r+1} below degree n and Q_n′=n!h.
4. Identify successive complex derivatives of the scalarization by induction.
5. Differentiate once more and use locality to match the exact ofComplex extension.

## Reference use

### local-project

Queries:
- `rg --files --hidden -g AGENTS.md -g Submission.lean -g lakefile.lean -g lake-manifest.json -g lean-toolchain -g '*dag*' -g '*decomposition*' -g '*state*' -g '!**/.git/**' -g '!**/node_modules/**' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d .`
- `IsEichlerIntegral|IsEquivariantPrimitiveWith|coeffH1parMk_eq_zero_iff|p02_es_177ebb5a_`
- `p02_es_177ebb5a_|scalarization`
- `isZero_of_neg_weight|eq_const_of_weight_zero|exp_decay_atImInfty|isBoundedAt_iff|isCusp_SL2Z|isArithmetic_iff_finiteIndex`
- `Gamma0|FiniteIndex`
- `iteratedDeriv|def `
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_es_177ebb5a_typecheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/RemovableSingularity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/NormTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. rg was unavailable, so searches used grep. The defining files confirm the coefficientwise derivative predicate, constant-defect cocycle, existence branch, trace-squared parabolic test, and quotient by coboundaries. HasPrimitives supplies disk primitives; QExpansion supplies exponential decay; BoundedAtCusp supplies the full scaling-matrix criterion; NormTrace supplies negative-weight vanishing and weight-zero constancy. No scalarization helper matched in the searched P2M directory, and no proposed identifier matched the searched declarations or current DAG, which contains only the root. The six transitive project definition files matched the snapshot; all installed dependencies matched their pinned revisions with clean tracked sources. All five proposed types elaborated under Lean 4.33.1 with only import Submission. Their elaborated modular-form groups use the prescribed mapGL image of Gamma0. Axiom checks of the reused primitive, representation, quotient, decay, cusp, and weight theorems returned only propext, Classical.choice, and Quot.sound. These are interface and library checks, not comparator acceptance of any new proof.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
