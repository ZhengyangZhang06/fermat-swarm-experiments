<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1.lct_monomial_expansion-a1 -->

## Theorem `Submission.p02_es_177ebb5a_ic_lct_monomial_expansion`

Let n be a natural number and Q an element of HeckeEis.BinaryForm ℂ n. For r ∈ Fin(n+1), define d_r : Fin 2 →₀ ℕ by d_r = Finsupp.single 0 r.val + Finsupp.single 1 (n−r.val). Then, in MvPolynomial (Fin 2) ℂ, Q.val = Σ_{r∈Fin(n+1)} coeff d_r(Q.val) • monomial d_r 1.

Node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1.lct_monomial_expansion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/115

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_ic_lct_monomial_expansion`

```lean
∀ (n : ℕ) (Q : ↥(HeckeEis.BinaryForm ℂ n)), Q.val = ∑ r : Fin (n + 1), MvPolynomial.coeff (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val)) Q.val • MvPolynomial.monomial (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val)) (1 : ℂ)
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
- Child DAG node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.linear_coefficient_transport-a1.lct_monomial_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n and Q. For r ∈ Fin(n+1), put d_r = single 0 r.val + single 1 (n−r.val), and put m_r = monomial d_r 1. Since r.val < n+1, we have r.val ≤ n. Evaluating the single functions gives d_r(0)=r.val and d_r(1)=n−r.val. The degree of a finitely supported exponent on Fin 2 is the sum of its values at 0 and 1, so degree(d_r)=r.val+(n−r.val)=n.
2. Let S = Σ_r coeff d_r(Q.val) • m_r. Fix any exponent d : Fin 2 →₀ ℕ. Coefficients preserve finite sums and scalar multiplication, and the monomial coefficient formula gives coeff d(m_r)=1 if d_r=d and 0 otherwise. Consequently coeff d(S)=Σ_r coeff d_r(Q.val)·(if d_r=d then 1 else 0).
3. Suppose degree(d)≠n. Since Q belongs to the degree-n homogeneous submodule, coeff d(Q.val)=0. Step 1 shows d_r≠d for every r, so every summand in step 2 is zero. Thus coeff d(S)=0=coeff d(Q.val).
4. Suppose degree(d)=n. This means d(0)+d(1)=n. Hence d(0)≤n and n−d(0)=d(1). Let r₀ ∈ Fin(n+1) have value d(0); its required bound follows from d(0)≤n. The exponents d_{r₀} and d agree at 0 and at 1. These are all elements of Fin 2, so finitely supported function extensionality gives d_{r₀}=d.
5. If d_r=d, evaluation at 0 gives r.val=d(0)=r₀.val. Extensionality of Fin yields r=r₀. Therefore the finite sum in step 2 reduces to its term at r₀ and equals coeff d_{r₀}(Q.val)=coeff d(Q.val).
6. The two cases prove coeff d(Q.val)=coeff d(S) for every exponent d. Polynomial coefficient extensionality gives Q.val=S, which is the asserted equality.

## Key steps

1. Compute the coordinates and degree of every exponent d_r.
2. Compute coefficients of the proposed sum using coefficient linearity and the monomial formula.
3. Use homogeneity to handle exponents of degree different from n.
4. Represent each degree-n exponent uniquely as d_r.
5. Reduce the coefficient sum to one term and apply polynomial extensionality.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/180

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
