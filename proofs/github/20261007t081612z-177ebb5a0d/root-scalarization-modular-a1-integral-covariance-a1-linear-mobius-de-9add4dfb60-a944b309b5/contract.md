<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1 -->

## Theorem `Submission.p02_es_177ebb5a_ic_lmd_linear_coeff`

Let n be a natural number, V = HeckeEis.BinaryForm ℂ n, A : V → V a complex-linear map, F : ℍ → V, P ∈ V, and τ ∈ ℍ. Suppose that for every exponent index d : Fin 2 →₀ ℕ, the complex-valued function z ↦ coeff d(F(ofComplex z)) has complex derivative coeff d(P) at (τ : ℂ). Then for every exponent index e, z ↦ coeff e(A(F(ofComplex z))) has complex derivative coeff e(A(P)) at (τ : ℂ).

Node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/98

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/140, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/141

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_ic_lmd_linear_coeff`

```lean
∀ (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n)) (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (P : ↥(HeckeEis.BinaryForm ℂ n)) (τ : UpperHalfPlane), (∀ d : Fin 2 →₀ ℕ, HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val) (MvPolynomial.coeff d P.val) (τ : ℂ)) → ∀ e : Fin 2 →₀ ℕ, HasDerivAt (fun z : ℂ => MvPolynomial.coeff e (A (F (UpperHalfPlane.ofComplex z))).val) (MvPolynomial.coeff e (A P).val) (τ : ℂ)
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

- Parent DAG node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1`
- Child DAG node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, A, F, P, τ and the assumed derivatives. Set t = (τ : ℂ). For each r ∈ {0,…,n}, define d_r = Finsupp.single 0 r + Finsupp.single 1 (n−r). Its values at 0 and 1 are r and n−r, respectively, so its total degree is r+(n−r)=n. Hence the monomial with exponent d_r and coefficient 1 is homogeneous of degree n. Let b_r ∈ V denote this monomial viewed in the homogeneous submodule.
2. For every Q ∈ V, prove Q = Σ_{r=0}^n coeff d_r(Q) • b_r by comparing polynomial coefficients. Fix any exponent index d. Its degree is d(0)+d(1). If this is not n, homogeneity gives coeff d(Q)=0. Every d_r has degree n, so d differs from every d_r and every summand also has coefficient zero at d. If d(0)+d(1)=n, set r=d(0). Then r≤n and d(1)=n−r. Since Fin 2 consists of 0 and 1, equality at these coordinates gives d=d_r. Moreover, d=d_s implies s=d(0)=r. The monomial coefficient formula therefore reduces the coefficient of the sum to the unique term coeff d_r(Q), which equals coeff d(Q). Polynomial coefficient extensionality gives equality of the underlying polynomials, and subtype extensionality gives equality in V.
3. Fix an arbitrary output exponent e and define λ_r = coeff e(A(b_r)). Applying A to the expansion in step 2, using its preservation of finite sums and complex scalar multiplication, and then taking coefficient e gives coeff e(A(Q)) = Σ_{r=0}^n coeff d_r(Q) · λ_r = Σ_{r=0}^n λ_r · coeff d_r(Q) for every Q ∈ V. The final equality uses commutativity of multiplication in ℂ.
4. Apply this identity to Q=F(ofComplex z) for each complex z. Thus the function whose derivative is sought equals Σ_{r=0}^n λ_r · coeff d_r(F(ofComplex z)). The hypothesis at d_r gives derivative coeff d_r(P) at t for its input coefficient function. Multiplication by the fixed scalar λ_r gives derivative λ_r · coeff d_r(P). The finite-sum derivative rule gives derivative Σ_{r=0}^n λ_r · coeff d_r(P) for the displayed sum at t.
5. Apply the identity in step 3 to Q=P. It identifies that derivative with coeff e(A(P)). Substitute the function identity from step 4 and this derivative identity to obtain the asserted HasDerivAt statement. Since e was arbitrary, the conclusion holds for every exponent index, without any restriction on its degree.

## Key steps

1. Construct the n+1 degree-n monomials as elements of the homogeneous submodule.
2. Prove the finite coefficient expansion by coefficient extensionality and uniqueness of the degree-n exponent pair.
3. Express each output coefficient of A as a fixed finite linear combination of input coefficients.
4. Differentiate that finite linear combination using the hypotheses.
5. Evaluate the same coefficient identity at P to identify the derivative.

## Reference use

### local-project

Queries:
- `BinaryForm|eventuallyEq_coe_comp_ofComplex|hasStrictDerivAt_smul`
- `basis|monomial|finite|coeff`
- `linear_coeff_derivative|linear_mobius_derivative|scalar_pullback`
- `theorem HasDerivAt.(sum|fun_sum|const_mul|comp)|lemma HasDerivAt.(sum|fun_sum|const_mul|comp)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous polynomial submodule. The inspected sources supply homogeneous monomials, vanishing coefficients outside the specified degree, jFactor_eq_denom, jFactor_ne_zero, hasStrictDerivAt_smul, ofComplex_apply, and scalar sum, multiplication, and chain rules. The project search for linear_coeff_derivative|linear_mobius_derivative|scalar_pullback returned no matches. The two inspected project definitions and three inspected homogeneous/upper-half-plane mathlib files match the installed sources byte-for-byte; installed mathlib has the pinned revision and clean Git status. Axiom queries for the six cited homogeneous, jFactor, and upper-half-plane lemmas returned only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/333

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
