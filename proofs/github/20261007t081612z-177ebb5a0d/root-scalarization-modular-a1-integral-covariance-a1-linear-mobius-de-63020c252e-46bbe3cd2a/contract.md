<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1.lct_coefficient_expansion-a1 -->

## Theorem `Submission.p02_es_177ebb5a_ic_lct_coeff_linear_combination`

Let n be a natural number, V = HeckeEis.BinaryForm ℂ n, A : V →ₗ[ℂ] V, and e : Fin 2 →₀ ℕ. For r ∈ Fin(n+1), put d_r = Finsupp.single 0 r.val + Finsupp.single 1 (n−r.val). There exists c : Fin(n+1) → ℂ, independent of Q, such that every Q ∈ V satisfies coeff e((A Q).val) = Σ_{r∈Fin(n+1)} c(r)·coeff d_r(Q.val).

Node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1.lct_coefficient_expansion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/115

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/140

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_ic_lct_coeff_linear_combination`

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

- Parent DAG node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1`
- Child DAG node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1.lct_coefficient_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, A, and e, and write V=HeckeEis.BinaryForm ℂ n. For each r ∈ Fin(n+1), define d_r=single 0 r.val+single 1 (n−r.val) and m_r=monomial d_r 1. We have r.val≤n, d_r(0)=r.val, and d_r(1)=n−r.val, so degree(d_r)=n. The monomial coefficient formula shows that every nonzero coefficient of m_r has exponent d_r and therefore degree n. Thus m_r is homogeneous of degree n. Let b_r ∈ V be m_r regarded as an element of this homogeneous submodule.
2. Define c(r)=coeff e((A b_r).val). This defines c : Fin(n+1) → ℂ using only n, A, and e, before any choice of Q.
3. Fix Q ∈ V and set a_r=coeff d_r(Q.val). Apply lct_monomial_expansion to obtain Q.val=Σ_r a_r • m_r. The inclusion of V into MvPolynomial (Fin 2) ℂ preserves finite sums and scalar multiplication. Therefore this sum is the underlying polynomial of Σ_r a_r • b_r. Subtype extensionality now gives Q=Σ_r a_r • b_r in V.
4. Apply A to the equality in step 3. Since A is complex linear, it preserves the finite sum and each scalar multiple, giving A Q=Σ_r a_r • A b_r. Taking underlying polynomials and then coefficient e, using coefficient additivity and scalar compatibility, gives coeff e((A Q).val)=Σ_r a_r·coeff e((A b_r).val).
5. Substitute a_r=coeff d_r(Q.val) and the definition of c(r). Commutativity of complex multiplication changes each summand to c(r)·coeff d_r(Q.val). This proves the required identity for the arbitrary Q. Hence the function c defined in step 2 satisfies the universal identity and witnesses the existential conclusion.

## Key steps

1. Construct the degree-n monomials as elements b_r of the homogeneous submodule.
2. Define c(r) as the output coefficient of A(b_r), independently of Q.
3. Use the sibling expansion and subtype extensionality to expand Q inside V.
4. Apply linearity of A and of the coefficient functional.
5. Commute the complex factors and conclude the identity for every Q.

## Reference use

### local-project

Queries:
- `binaryForm.*(basis|[Ee]xpan|[Cc]oeff)|BinaryForm.*(basis|[Ee]xpan)|coeff.*HasDerivAt|HasDerivAt.*coeff`
- `BinaryForm.*(expand|expansion|sum)|((expand|expansion|sum).*[Bb]inary[Ff]orm)`
- `basis|monomial|coeff.*zero|sum|mem_homogeneousSubmodule`
- `theorem (coeff_monomial|coeff_smul|coeff_sum|ext)|lemma (coeff_monomial|coeff_smul|coeff_sum)|finsetSum_coeff|support_sum_monomial_coeff`
- `degree_eq_sum|degree_single|degree_add|degree_eq_weight_one`
- `theorem HasDerivAt\.(sum|fun_sum|const_mul)|lemma HasDerivAt\.(sum|fun_sum|const_mul)`
- `p02_es_177ebb5a_ic_lct_monomial_expansion|p02_es_177ebb5a_ic_lct_coeff_linear_combination`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_ic_lct_decomposition_types.lean`

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
- `/tmp/p02_ic_lct_decomposition_types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous polynomial submodule. The project search found the coefficientwise Eichler-integral derivative condition; the specialized binary-form expansion search returned no matches in project/Definitions or mathlib/Mathlib/RingTheory/MvPolynomial. Inspected mathlib sources supply monomial homogeneity, off-degree coefficient vanishing, coefficient extensionality and linearity, exponent degree identities, and finite-sum and constant-multiple derivative rules. Both proposed types elaborated after import Submission. Instance synthesis returned AddMonoidAlgebra.algebra.toSMul for polynomial scalar multiplication and the submodule scalar action for BinaryForm; coefficient compatibility with complex multiplication also checked. All nine installed dependencies matched their pins with clean tracked sources. Six transitive project definition files matched the frozen project revision and snapshot, and the five inspected mathlib files matched the snapshot. Transitive axiom checks of the cited infrastructure returned only propext, Classical.choice, and Quot.sound. Equivalent algebraic obligations remain pending under other names in another DAG branch; neither proposed identifier is reserved. These are interface and infrastructure checks, not comparator acceptance of child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/208

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
