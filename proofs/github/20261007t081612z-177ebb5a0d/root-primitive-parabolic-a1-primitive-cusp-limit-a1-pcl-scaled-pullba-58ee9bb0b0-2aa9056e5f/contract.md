<!-- theorem-id: fermat-p02/root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scaled_pullback_derivative-a1 -->

## Theorem `Submission.p02_es_177ebb5a_pcl_scaled_pullback_derivative`

Let n be a natural number, f:ℍ→ℂ, and F:ℍ→BinaryForm ℂ n. Assume IsEichlerIntegral n f F: for every monomial exponent e and τ∈ℍ, the function z↦coeff_e(F(ofComplex z)) has complex derivative f(τ)coeff_e((τX+Y)^n) at τ. For every σ∈SL₂(ℤ), exponent d, and τ∈ℍ, the function z↦coeff_d(F(σ·ofComplex z)) has complex derivative j(σ,τ)^{−(n+2)}f(σ·τ)coeff_d(binaryFormRepSL ℂ n σ ((τX+Y)^n)) at τ, where j(σ,τ)=σ₁₀τ+σ₁₁.

Node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scaled_pullback_derivative-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/71

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_pcl_scaled_pullback_derivative`

```lean
∀ (n : ℕ) (f : UpperHalfPlane → ℂ) (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n f F → ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : Fin 2 →₀ ℕ) (τ : UpperHalfPlane), HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (σ • UpperHalfPlane.ofComplex z)).val) ((HeckeEis.jFactor σ τ) ^ (-((n : ℤ) + 2)) * f (σ • τ) * MvPolynomial.coeff d ((HeckeEis.binaryFormRepSL ℂ n σ) (HeckeEis.linePow n (τ : ℂ))).val) (τ : ℂ)
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

- Parent DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1`
- Child DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scaled_pullback_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, f, F, the Eichler-integral hypothesis, σ, d, and τ. Write the entries of σ as α, β, γ, δ, so αδ−βγ=1, and put j=γτ+δ. The denominator j is nonzero on the upper half-plane. Define m(z)=(αz+β)/(γz+δ), L(z)=(zX+Y)^n, and R=binaryFormRepSL ℂ n σ.
2. On the open upper half-plane, m(z) is the complex coordinate of σ·ofComplex z. Its image also lies in the upper half-plane. Thus, in a neighborhood of τ, ofComplex(m(z))=σ·ofComplex z. In particular, for φ(w)=coeff_d(F(ofComplex w)), the function in the conclusion agrees locally with φ∘m. The Eichler-integral hypothesis at σ·τ gives φ'(m(τ))=f(σ·τ)coeff_d(L(m(τ))).
3. The quotient rule applies at τ because j≠0. It gives m'(τ)=(α(γτ+δ)−γ(ατ+β))/j²=(αδ−βγ)/j²=j^(−2). The complex chain rule therefore gives the derivative of the required coefficient function as f(σ·τ)coeff_d(L(m(τ)))j^(−2).
4. The identity binaryFormRepSL_linePow gives R(L(τ))=j^n L(m(τ)). Taking the d-coefficient, using its complex linearity, gives coeff_d(R(L(τ)))=j^n coeff_d(L(m(τ))).
5. Since j≠0, multiplication of integer powers gives j^{−(n+2)}j^n=j^(−2). Consequently j^{−(n+2)}f(σ·τ)coeff_d(R(L(τ))) equals the derivative obtained in step 3. Local equality preserves HasDerivAt, so this proves exactly the asserted derivative for the total function using ofComplex.

## Key steps

1. Identify the pullback locally with composition by the Möbius rational function.
2. Differentiate the Möbius function using determinant one and its nonzero denominator.
3. Apply the coefficientwise Eichler-integral hypothesis and chain rule.
4. Take coefficients in binaryFormRepSL_linePow.
5. Combine the integer powers of the nonzero automorphy factor.

## Reference use

### local-project

Queries:
- `scaled_cusp_decay|IsEichlerIntegral|binaryFormRepSL|eichlerShimuraMap_injective`
- `hasDerivAt|ofComplex|coe_specialLinearGroup_apply`
- `integrableOn.*exp|integrableOn.*rpow|tendsto.*exp.*atTop`
- `sum_monomial_eq|coeff_sum|coeff_smul|coeff_monomial|coeff_mul_X|coeff_add`
- `scaled_cusp_decay|common_ray_limit|linear_linepow_growth`
- `sed -n '35,135p' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_pcl_decomposition_checks/Check.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The installed mathlib HEAD matches and has no tracked modifications; both inspected HeckeEis definition files match the snapshot byte-for-byte. The snapshot supplies coefficientwise IsEichlerIntegral, binaryFormRepSL_linePow, jFactor_ne_zero, the local ofComplex identities, the Möbius derivative, coefficient linearity, homogeneous support, exponential asymptotics, and the fundamental theorem of calculus. Searching the snapshot for scaled_cusp_decay|common_ray_limit|linear_linepow_growth returned no matches; scaled_cusp_decay is an existing parent DAG dependency. All three proposed types elaborated after import Submission. Transitive axiom checks of binaryFormRepSL_linePow, jFactor_ne_zero, hasStrictDerivAt_smul, integral_eq_sub_of_hasDerivAt, and tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero returned only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/213

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
