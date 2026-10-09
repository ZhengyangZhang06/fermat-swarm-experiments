<!-- theorem-id: fermat-p02/root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1.linear_map_coefficient_expansion-a1 -->

## Theorem `Submission.p02_es_177ebb5a_lcd_coeff_linear_combination`

Let n∈ℕ, let V=BinaryForm ℂ n, let A:V→V be complex linear, and let e:Fin 2→₀ℕ be any exponent index. For r∈Fin(n+1), put d_r=single 0 r.val+single 1 (n−r.val). There exists a function c:Fin(n+1)→ℂ, depending only on n, A, and e, such that for every Q∈V, coeff e((A Q).val)=Σ_{r∈Fin(n+1)} c(r)·coeff d_r(Q.val).

Node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1.linear_map_coefficient_expansion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/50

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/92

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_lcd_coeff_linear_combination`

```lean
∀ (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n)) (e : Fin 2 →₀ ℕ), ∃ c : Fin (n + 1) → ℂ, ∀ Q : ↥(HeckeEis.BinaryForm ℂ n), MvPolynomial.coeff e (A Q).val = ∑ r : Fin (n + 1), c r * MvPolynomial.coeff (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val)) Q.val
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

- Parent DAG node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1`
- Child DAG node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1.linear_map_coefficient_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, A, and e. For each r∈Fin(n+1), define d_r=single 0 r.val+single 1 (n−r.val). Since r.val≤n, its degree is r.val+(n−r.val)=n. The monomial m_r=monomial d_r 1 is therefore homogeneous of degree n, by monomial homogeneity. Thus b_r=⟨m_r, its membership proof⟩ is an element of V=BinaryForm ℂ n.
2. Define c(r)=coeff e((A b_r).val). This defines a function Fin(n+1)→ℂ before choosing Q, so it is independent of Q.
3. Fix any Q∈V and write a_r=coeff d_r(Q.val). Apply binary_form_monomial_expansion to obtain Q.val=Σ_r a_r • m_r. The inclusion of the submodule V into the polynomial space preserves finite sums and scalar multiplication, so the right side is the underlying polynomial of Σ_r a_r • b_r. Injectivity of this inclusion, or subtype extensionality, gives Q=Σ_r a_r • b_r in V.
4. Apply A to this equality. Additivity and complex linearity give A Q=Σ_r a_r • A b_r. Taking underlying polynomials and then coefficient e, and using coefficient additivity and compatibility with scalar multiplication, gives coeff e((A Q).val)=Σ_r a_r·coeff e((A b_r).val).
5. Substitute the definitions of a_r and c(r), and commute the two complex factors in each summand. The result is coeff e((A Q).val)=Σ_r c(r)·coeff d_r(Q.val). Since Q was arbitrary, the function c from step 2 satisfies the required universal identity, proving the existential conclusion.

## Key steps

1. Construct the degree-n monomials as elements of the homogeneous submodule.
2. Define the fixed output coefficients c(r) by applying A to those monomials.
3. Lift the sibling's polynomial expansion to an equality inside BinaryForm.
4. Apply the linear map and then the coefficient functional.
5. Commute complex scalar factors and conclude the uniform identity for every Q.

## Reference use

### local-project

Queries:
- `binaryForm.*(basis|[Ee]xpan|[Cc]oeff)|BinaryForm.*(basis|[Ee]xpan)|coeff.*HasDerivAt|HasDerivAt.*coeff`
- `basis|coeff_eq_zero|isHomogeneous_monomial|homogeneousSubmodule|sum_monomial|def IsHomogeneous`
- `theorem (coeff_monomial|coeff_smul|coeff_sum|ext)|lemma (coeff_monomial|coeff_smul|coeff_sum)|finsetSum_coeff|degree_eq_sum|degree_single|degree_add|degree_eq_weight_one`
- `theorem HasDerivAt.(sum|const_mul)|lemma HasDerivAt.(sum|const_mul)`
- `p02_es_177ebb5a_lcd_monomial_expansion|p02_es_177ebb5a_lcd_coeff_linear_combination`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_lcd_decomposition_types.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Finsupp/Weight.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/tmp/p02_lcd_decomposition_types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous polynomial submodule. The project search found the defining coefficientwise IsEichlerIntegral condition but no matching binary-form expansion or derivative helper. Mathlib supplies monomial homogeneity, off-degree coefficient vanishing, coefficient extensionality and linearity, exponent degree identities, HasDerivAt.fun_sum, and HasDerivAt.const_mul. Neither proposed identifier occurred in the searched project or run metadata. Both exact proposed types elaborated after import Submission under Lean 4.33.1. Instance synthesis confirmed the polynomial scalar action is AddMonoidAlgebra.algebra.toSMul. All installed dependencies matched their pinned revisions with clean tracked sources; the six transitive project definition files and five inspected mathlib files matched the snapshot byte-for-byte. Transitive axiom checks of the cited infrastructure returned only propext, Classical.choice, and Quot.sound. These checks validate the interfaces and infrastructure, not comparator acceptance of the proposed children.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/188

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
