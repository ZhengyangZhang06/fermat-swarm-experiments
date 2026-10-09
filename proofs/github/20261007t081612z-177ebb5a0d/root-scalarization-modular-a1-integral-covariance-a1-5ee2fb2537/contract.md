<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.integral_covariance-a1 -->

## Theorem `Submission.p02_es_177ebb5a_sm_transformed_integral`

Let n∈ℕ, h:ℍ→ℂ, E:ℍ→BinaryForm ℂ n, and σ∈SL₂(ℤ). If IsEichlerIntegral n h E holds, then G(z)=binaryFormRepSL ℂ n (σ⁻¹)(E(σz)) satisfies IsEichlerIntegral n (h|_{n+2}σ) G.

Node: `root.scalarization_modular-a1.integral_covariance-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/28

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/98, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/99

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_sm_transformed_integral`

```lean
∀ (n : ℕ) (h : UpperHalfPlane → ℂ) (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ), HeckeEis.IsEichlerIntegral n h E → HeckeEis.IsEichlerIntegral n (SlashAction.map ((n : ℤ) + 2) σ h) (fun τ : UpperHalfPlane => ((HeckeEis.binaryFormRepSL ℂ n) σ⁻¹) (E (σ • τ)))
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

- Parent DAG node: `root.scalarization_modular-a1`
- Child DAG node: `root.scalarization_modular-a1.integral_covariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write ρ=binaryFormRepSL ℂ n and L(z)=(zX+Y)^n. Work on U={z∈ℂ:Im z>0}. At each point of U, ofComplex agrees locally with the usual identification with ℍ, as recorded in Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean. The hypothesis therefore says coefficientwise that E′(z)=h(z)L(z).
2. Fix z∈U, write σ=(a b;c d), and put j=cz+d and w=(az+b)/j. The determinant-one identity ensures j≠0 and Im w=Im z/|j|²>0. Differentiating the quotient gives w′=(ad−bc)/j²=j^(−2). The corresponding derivative of the ofComplex extension is also supplied by UpperHalfPlane.hasStrictDerivAt_smul in Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean.
3. The degree-n homogeneous monomials form a finite basis. A fixed linear substitution, such as ρ(σ⁻¹), expresses every output coefficient as a finite linear combination of input coefficients. Thus the ordinary chain rule and linearity of differentiation give G′(z)=h(w)j^(−2)ρ(σ⁻¹)L(w), coefficientwise.
4. HeckeEis.binaryFormRepSL_linePow in Definitions/Def_HeckeEis_EichlerIntegral.lean gives ρ(σ)L(z)=j^nL(w). Apply ρ(σ⁻¹), use its linearity and the representation inverse law, and divide by j^n. This yields ρ(σ⁻¹)L(w)=j^(−n)L(z).
5. Combining steps 3 and 4 gives G′(z)=h(w)j^(−(n+2))L(z). By ModularForm.SL_slash_apply in Mathlib/NumberTheory/ModularForms/SlashActions.lean, the scalar factor is exactly (h|_{n+2}σ)(z).
6. These calculations hold for every coefficient index. Indices outside total degree n have identically zero coefficients on both sides, and the finite homogeneous expansion handles every index of degree n. At each τ∈ℍ, locality of ofComplex identifies these derivatives with the precise functions quantified by IsEichlerIntegral. Hence G satisfies the stated predicate, without any additional regularity hypothesis on h.

## Key steps

1. Interpret the given derivative predicate locally on the open upper half-plane.
2. Differentiate the determinant-one Möbius transformation.
3. Commute the fixed finite linear substitution with coefficient differentiation.
4. Apply the line-power representation identity.
5. Identify the resulting scalar factor with the weight n+2 slash action.
6. Translate the coefficient identities back to the exact IsEichlerIntegral predicate.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|binaryFormRepSL_linePow|eval_smul_of_isHomogeneous|binaryFormRepSL_apply_coe`
- `exp_decay_atImInfty|isBoundedAt_iff|isCusp_SL2Z_iff|isCusp_iff_isCusp_SL2Z|isArithmetic_iff_finiteIndex|instFiniteIndexGamma0|Gamma_normal|ModularGroup_T_pow_mem_Gamma`
- `scalarization|equivariant.*bounded|p02_es_177ebb5a_sm_`
- `hasStrictDerivAt_smul|Gamma_le_Gamma0|MDifferentiable.slash|isBoundedAtImInfty_iff`
- `def ofComplex|ofComplex_apply|ofComplex.*vadd|vadd.*ofComplex`
- `/runtime/bin/rg -n 'p02_es_177ebb5a_sm_' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project Submission.lean Definitions Theorems P2M Fermat .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_sm_typecheck.lean`
- `git -C .lake/packages/mathlib status --short`
- `git -C .lake/packages/mathlib rev-parse HEAD`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`

The snapshot pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Searches used /runtime/bin/rg after locating it outside PATH. The definitions confirm coefficientwise differentiation, the substitution convention, homogeneity, and the line-power transformation identity. Mathlib supplies the precise SL₂ slash action, exponential decay with periodicity/holomorphy/boundedness hypotheses, arithmetic cusp classification, and the full single-scaling-matrix criterion. No existing scalarization or equivariant-boundedness helper matched in the searched project directories; the proposed identifier prefix matched neither project declarations nor active DAG records. All five exact types elaborated after import Submission under Lean 4.33.1. Instance inspection returned ModularForm.SLAction, and the explicit real subgroup image uses Matrix.semiring. The installed dependency revisions match their pins with clean tracked sources; the transitive project definition files and inspected mathlib interfaces match the snapshot. Axiom queries for the reused representation, homogeneity, manifold, slash, decay, finite-index, and cusp results returned only propext, Classical.choice, and Quot.sound. These are interface and provenance checks, not comparator acceptance of new proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/557

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
