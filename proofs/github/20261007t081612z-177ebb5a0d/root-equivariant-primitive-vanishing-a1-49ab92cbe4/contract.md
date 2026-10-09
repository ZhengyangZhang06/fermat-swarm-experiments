<!-- theorem-id: fermat-p02/root.equivariant_primitive_vanishing-a1 -->

## Theorem `Submission.p02_es_177ebb5a_equivariant_primitive_vanishes`

Let N,n∈ℕ with N≠0, Γ=Γ₀(N), and ρ the restricted degree-n binary-form representation. If f is a weight n+2 cusp form and E : ℍ → BinaryForm ℂ n satisfies IsEichlerIntegral n f E and E(γz)=ρ(γ)E(z) for every γ∈Γ and z∈ℍ, then f=0 as a bundled cusp form.

Node: `root.equivariant_primitive_vanishing-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/28, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/29

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_equivariant_primitive_vanishes`

```lean
∀ (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n (fun τ => f τ) E → (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane), E ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) = ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) γ (E τ)) → f = 0
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
- Child DAG node: `root.equivariant_primitive_vanishing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Apply the sibling theorem p02_es_177ebb5a_scalarization_modular with the given N,n,f,E, derivative predicate, and exact equivariance. It supplies a bundled modular form p of weight −n with p(τ)=E(τ)(1,−τ) for every τ∈ℍ.
2. The hypothesis N≠0 gives the finite-index instance CongruenceSubgroup.instFiniteIndexGamma0 from Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean. Equivalently, the kernel of reduction modulo N has finite index and lies in Γ₀(N). Subgroup.isArithmetic_iff_finiteIndex from ArithmeticSubgroups.lean therefore makes the prescribed real matrix image of Γ₀(N) arithmetic. This checks the group hypothesis of the weight theorems used next.
3. If n>0, then −(n:ℤ)<0. Apply ModularForm.isZero_of_neg_weight from Mathlib/NumberTheory/ModularForms/NormTrace.lean to p; it gives p=0. If n=0, its weight is zero, and ModularForm.eq_const_of_weight_zero from the same file gives a scalar c with p constantly equal to c. Thus in either case p is constant on ℍ.
4. Define P(z)=E(ofComplex z)(1,−z). At any τ∈ℍ choose an open neighborhood contained in the upper half-plane. On that neighborhood, step 1 identifies P with the constant function from step 3. Hence its complex derivative of the positive order n+1 is zero at τ. This follows either by successive differentiation of a constant or by iteratedDeriv_const and locality of derivatives.
5. The cusp-form holomorphy hypothesis, converted through UpperHalfPlane.mdifferentiable_iff, supplies DifferentiableOn ℂ (fun z => f (ofComplex z)) on {z | 0<z.im}. Apply the sibling theorem p02_es_177ebb5a_scalarization_derivative with h=f and the given IsEichlerIntegral proof. Together with step 4 it gives ((-1:ℂ)^n·(n!:ℂ))f(τ)=0 for every τ∈ℍ.
6. The scalar (-1:ℂ)^n is nonzero. The positive natural number n! has nonzero image in the characteristic-zero field ℂ, so their product is nonzero. Cancellation gives f(τ)=0 for every τ. Extensionality of bundled cusp forms now gives f=0, as asserted.

## Key steps

1. Use scalarization_modular to obtain a modular form of weight −n.
2. Verify arithmeticity from the finite index of Γ₀(N).
3. Apply pinned negative-weight vanishing or weight-zero constancy.
4. Conclude that the scalarization's derivative of order n+1 vanishes locally.
5. Apply scalarization_derivative and cancel the nonzero factorial factor.
6. Use cusp-form extensionality.

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

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
