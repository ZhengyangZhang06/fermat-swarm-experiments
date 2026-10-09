<!-- theorem-id: fermat-p02/root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1 -->

## Theorem `Submission.p02_es_177ebb5a_cd_linear_coeff_derivative`

Let n∈ℕ and V=BinaryForm ℂ n, the complex vector space of homogeneous binary polynomials of degree n. Let A:V→V be complex linear, F:ℂ→V, P∈V, and z∈ℂ. Suppose that for every exponent index d:Fin 2→₀ℕ, the scalar function w↦coeff d(F(w)) has complex derivative coeff d(P) at z. Then, for every exponent index e, the scalar function w↦coeff e(A(F(w))) has complex derivative coeff e(A(P)) at z.

Node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/39

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/92, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/94

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_cd_linear_coeff_derivative`

```lean
∀ (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n)) (F : ℂ → ↥(HeckeEis.BinaryForm ℂ n)) (P : ↥(HeckeEis.BinaryForm ℂ n)) (z : ℂ), (∀ e : Fin 2 →₀ ℕ, HasDerivAt (fun w : ℂ => MvPolynomial.coeff e (F w).val) (MvPolynomial.coeff e P.val) z) → ∀ e : Fin 2 →₀ ℕ, HasDerivAt (fun w : ℂ => MvPolynomial.coeff e (A (F w)).val) (MvPolynomial.coeff e (A P).val) z
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

- Parent DAG node: `root.primitive_exists-a1.constant_defect-a1`
- Child DAG node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n,A,F,P,z and the assumed derivatives. For each integer r with 0≤r≤n, define the exponent index d_r by d_r(0)=r and d_r(1)=n−r. Its total degree is n. Let b_r be the monomial with exponent d_r and coefficient 1, regarded as an element of V; it belongs to V because that monomial is homogeneous of degree n.
2. Every Q∈V satisfies Q=Σ_{r=0}^n coeff d_r(Q) • b_r. To prove this, compare coefficients at an arbitrary exponent index d. Its total degree is d(0)+d(1). If this degree differs from n, homogeneity makes coeff d(Q)=0, and every b_r also has coefficient zero at d. If the degree equals n, let r=d(0). Then r≤n and d(1)=n−r, so d=d_r. No other d_s equals d, since equality at coordinate 0 would force s=r. Thus the coefficient of the displayed sum at d is exactly coeff d(Q). Polynomial coefficient extensionality, followed by subtype extensionality, proves the expansion.
3. Fix an output exponent index e and put λ_r=coeff e(A(b_r)). Apply A to the expansion of Q, use its additivity and complex linearity, and then take coefficient e. Linearity of polynomial coefficients and commutativity of complex multiplication give coeff e(A(Q))=Σ_{r=0}^n λ_r·coeff d_r(Q).
4. Apply this identity to Q=F(w) for every w∈ℂ. By hypothesis, each function w↦coeff d_r(F(w)) has derivative coeff d_r(P) at z. Multiplication by the constant λ_r and the finite-sum derivative rule therefore give derivative Σ_{r=0}^n λ_r·coeff d_r(P) for w↦coeff e(A(F(w))) at z. No topology on V is used: all differentiated functions are complex-valued.
5. Apply the identity from step 3 to Q=P. It identifies the derivative in step 4 with coeff e(A(P)). Since e was arbitrary, this is the asserted coefficientwise derivative statement.

## Key steps

1. Construct the degree-n monomials indexed by r=0,…,n.
2. Prove the finite monomial expansion by homogeneity and coefficient extensionality.
3. Express each output coefficient of A as a fixed finite linear combination of input coefficients.
4. Differentiate that finite scalar sum at z.
5. Identify the resulting sum with the corresponding coefficient of A(P).

## Reference use

### local-project

Queries:
- `rg -n 'IsEichlerIntegral|binaryFormRepSL_linePow|hasStrictDerivAt_smul' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b`
- `grep -R -n -E 'IsEichlerIntegral|IsEquivariantPrimitiveWith|binaryFormRepSL_linePow' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project --include='*.lean'`
- `hasDerivAt|ofComplex|convex`
- `slash_action_eqn_SL|slash_action_eqn`
- `coeff_eq_zero|mem_homogeneousSubmodule|IsHomogeneous|sum_monomial`
- `eq_of_hasDerivAt|eqOn_of_deriv|is_const|eq_of_deriv`
- `coeff.*HasDerivAt|HasDerivAt.*coeff|binaryForm.*[Dd]eriv|[Dd]eriv.*binaryForm`
- `p02_es_177ebb5a_cd_linear_coeff_derivative`
- `p02_es_177ebb5a_cd_modular_pullback_derivative`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_constant_defect_interfaces.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/tmp/p02_constant_defect_interfaces.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. rg was unavailable; searches continued with grep and Python. The definitions provide coefficientwise IsEichlerIntegral, jFactor_ne_zero, and binaryFormRepSL_linePow. Mathlib supplies homogeneous coefficient vanishing, the Möbius derivative, the determinant-one slash transformation law, and zero-derivative constancy. The project derivative-helper search found only the defining IsEichlerIntegral occurrence, with no matching helper. Neither proposed identifier occurred in the searched project declarations or run metadata. Both exact proposed types elaborated after import Submission under Lean 4.33.1. Explicit elaboration confirmed the mapGL image in the cusp-form type, matrix algebra instances, and UpperHalfPlane.SLAction. All installed dependencies matched their pinned revisions with clean tracked sources; the six transitive project definition files and inspected mathlib files matched the snapshot. Transitive axiom checks of the cited infrastructure returned only propext, Classical.choice, and Quot.sound. These checks validate interfaces and reusable infrastructure, not acceptance of new child proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/223

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
