<!-- theorem-id: fermat-p02/root.primitive_exists-a1.constant_defect-a1 -->

## Theorem `Submission.p02_es_177ebb5a_primitive_exists_constant_defect`

Let N,n∈ℕ with N≠0, let Γ=Γ₀(N), and let ρ be the restriction of binaryFormRepSL ℂ n to Γ. Let f be a cusp form of weight n+2 on the prescribed real matrix image of Γ, and let F : ℍ → BinaryForm ℂ n satisfy IsEichlerIntegral n f F. Then IsEquivariantPrimitiveWith ρ F holds: for every γ∈Γ there is c∈BinaryForm ℂ n such that F(γτ)−ρ(γ)F(τ)=c for every τ∈ℍ.

Node: `root.primitive_exists-a1.constant_defect-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/26

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/50, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/51

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_primitive_exists_constant_defect`

```lean
∀ (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n (fun τ => f τ) F → HeckeEis.IsEquivariantPrimitiveWith ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F
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

- Parent DAG node: `root.primitive_exists-a1`
- Child DAG node: `root.primitive_exists-a1.constant_defect-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N,n,f,F and the stated IsEichlerIntegral hypothesis. Put V=BinaryForm ℂ n, L(τ)=linePow n τ, and ρ=(binaryFormRepSL ℂ n).comp Γ.subtype. Fix γ∈Γ and write its underlying determinant-one integer matrix as g=(a b; c d). For τ∈ℍ write j(τ)=cτ+d. If c≠0, the imaginary part of j(τ) is c Im τ≠0. If c=0, the determinant relation ad−bc=1 forces d≠0. Thus j(τ) is always nonzero.
2. The Möbius transformation T(z)=(az+b)/(cz+d) satisfies Im T(z)=Im z/|cz+d|² on the upper half-plane, so it maps that domain into itself and represents the action of g there. Its complex derivative is (ad−bc)/(cz+d)²=1/(cz+d)². Around any τ∈ℍ, both the input and its image remain in the upper half-plane, where ofComplex has its usual complex coordinate. Consequently the coefficientwise chain rule applies to F(g·τ) using T′(τ)=j(τ)⁻².
3. Slash invariance of f on the prescribed mapGL image of Γ, specialized to g whose determinant is one, gives f(g·τ)=j(τ)^(n+2)f(τ). This is the transformation law supplied by SlashInvariantForm.slash_action_eqn_SL'', with the nonnegative integer exponent converted to a natural power. The pinned identity HeckeEis.binaryFormRepSL_linePow gives ρ(γ)L(τ)=j(τ)^n·L(g·τ).
4. We justify differentiating the representation coefficientwise without assigning a topology to V. For 0≤r≤n let e_r have entries r and n−r, and let m_r=X^rY^(n−r), regarded as an element of V. Every P∈V equals Σ_{r=0}^n coeff e_r(P)·m_r: homogeneity makes all coefficients outside total degree n vanish, and every degree-n exponent index on Fin 2 is uniquely e_r. Since ρ(γ) is complex linear, for every output exponent index e there are fixed scalars λ_{e,r}=coeff e(ρ(γ)m_r) such that coeff e(ρ(γ)P)=Σ_{r=0}^n λ_{e,r}coeff e_r(P). Applying IsEichlerIntegral to the finitely many input coefficients and differentiating this finite sum shows that the derivative at τ of coeff e(ρ(γ)F(ofComplex z)) is f(τ)coeff e(ρ(γ)L(τ)).
5. Apply IsEichlerIntegral at g·τ and the chain rule from step 2. The derivative at τ of z↦coeff e(F(g·ofComplex z)) is f(g·τ)coeff e(L(g·τ))j(τ)⁻². By step 3 and j(τ)≠0 this equals f(τ)j(τ)^n coeff e(L(g·τ))=f(τ)coeff e(ρ(γ)L(τ)). Thus it equals the derivative computed in step 4.
6. Define D(τ)=F(g·τ)−ρ(γ)F(τ). For every exponent index e, define the globally defined scalar function q_e(z)=coeff e(D(ofComplex z)). Subtracting the derivatives in steps 4 and 5 proves HasDerivAt q_e 0 τ for every τ∈ℍ. In particular q_e is complex differentiable, and hence continuous, on the upper half-plane.
7. Given τ,υ∈ℍ, set s(t)=(1−t)υ+tτ for real t∈[0,1]. Its imaginary part is (1−t)Im υ+t Im τ>0, so the whole segment lies in the upper half-plane. The composite q_e∘s is continuous on [0,1]. On (0,1), the real chain rule, obtained by restricting the zero complex derivative of q_e to real scalars, gives derivative zero. Its real and imaginary parts are therefore continuous on [0,1] with real derivative zero on (0,1). The real mean-value theorem makes their endpoint values equal. Hence coeff e(D(τ))=coeff e(D(υ)) for every e. Polynomial coefficient extensionality, followed by subtype extensionality, gives D(τ)=D(υ).
8. Take υ to be the upper-half-plane point i and choose c_γ=D(i)∈V. Step 7 yields F(g·τ)−ρ(γ)F(τ)=c_γ for every τ. Since γ was arbitrary, this is exactly IsEquivariantPrimitiveWith ρ F.

## Key steps

1. Establish the nonvanishing automorphy factor and the Möbius derivative.
2. Use slash invariance and binaryFormRepSL_linePow to identify the transformed differential.
3. Express each representation coefficient as a fixed finite linear combination of input coefficients.
4. Differentiate both terms of each modular defect and cancel their derivatives.
5. Apply the real mean-value theorem along upper-half-plane segments to every coefficient.
6. Use coefficient extensionality and the value at i to obtain the required constant.

## Reference use

### local-project

Queries:
- `rg -n 'IsEichlerIntegral|IsEquivariantPrimitiveWith|binaryFormRepSL_linePow|eichlerShimuraMap_injective|isExactOn_ball' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b`
- `grep -R -n -E 'IsEichlerIntegral|IsEquivariantPrimitiveWith|binaryFormRepSL_linePow|eichlerShimuraMap_injective|isExactOn_ball' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b --include='*.lean'`
- `upperHalfPlane.*(primitive|Primitive)|primitive.*upperHalfPlane|isExactOn_upperHalfPlane|p02_es_177ebb5a_primitive_exists_(scalar_primitive|holomorphic_integral|constant_defect)`
- `coeff_eq_zero|mem_homogeneousSubmodule|IsHomogeneous`
- `eqOn_of_deriv|eq_of_hasDerivAt|is_const|eq_of_deriv`
- `slash_action_eqn|slash_action_eq`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_primitive_exists_interfaces.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/tmp/p02_primitive_exists_interfaces.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. rg was unavailable, so searches used grep. The definitions confirm the coefficientwise IsEichlerIntegral predicate, constant-defect conclusion, and binaryFormRepSL_linePow identity. HasPrimitives supplies DifferentiableOn.isExactOn_ball; Manifold supplies the ofComplex holomorphy equivalence and Möbius derivative; SlashInvariantForms supplies the determinant-one transformation law; Homogeneous supplies coefficient vanishing outside the prescribed degree; MeanValue supplies zero-derivative constancy. The searched project Definitions/P2M and mathlib Analysis sources contained no upper-half-plane primitive theorem matching the stated search patterns. The proposed identifiers had no matches in the current declarations or node metadata. All three exact proposed types elaborated with only import Submission under Lean 4.33.1; explicit elaboration confirmed the prescribed mapGL image of Gamma0 and matrix algebra instances. All installed dependencies matched their recorded revisions with clean tracked sources; the six transitive project definition files and consulted mathlib files matched the snapshot. Axiom checks of the cited primitive, representation, transformation, derivative, constancy, and predicate declarations returned only propext, Classical.choice, and Quot.sound. These are interface and infrastructure checks, not comparator acceptance of new proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/459

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
