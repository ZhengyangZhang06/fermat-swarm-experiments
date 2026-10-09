<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.translation_bound-a1.translation_fixed_form-a1.periodic_polynomial_constant-a1 -->

## Theorem `Submission.p02_es_177ebb5a_tff_periodic_polynomial_constant`

For every polynomial p∈ℂ[t] and c∈ℂ with c≠0, if p(t+c)=p(t) as a polynomial identity, then p is the constant polynomial whose value is its coefficient at degree zero.

Node: `root.scalarization_modular-a1.translation_bound-a1.translation_fixed_form-a1.periodic_polynomial_constant-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/105

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_tff_periodic_polynomial_constant`

```lean
∀ (p : Polynomial ℂ) (c : ℂ), c ≠ 0 → p.comp (Polynomial.X + Polynomial.C c) = p → p = Polynomial.C (p.coeff 0)
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

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1.translation_fixed_form-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.translation_fixed_form-a1.periodic_polynomial_constant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix p∈ℂ[t] and c∈ℂ with c≠0, and assume p(t+c)=p(t). If p=0, its coefficient at zero is zero and the conclusion follows. Hence assume p≠0, let d be its degree, and write p(t)=Σ_{k=0}^d b_k t^k, where b_k is its k-th coefficient and b_d≠0.
2. Suppose d>0. Set q(t)=p(t+c)−p(t). The assumed identity gives q=0. By the binomial theorem, the coefficient of t^(d−1) in (t+c)^d−t^d is binomial(d,d−1)c=dc. Thus the leading term of p contributes b_d dc to that coefficient of q.
3. Every term with k<d contributes zero to the same coefficient. If k=d−1, the coefficients of t^k in (t+c)^k and t^k are both 1 and cancel, including when k=0. If k<d−1, neither polynomial has a term of degree d−1. Consequently the coefficient of t^(d−1) in q is exactly b_d(d:ℂ)c.
4. Since b_d≠0, c≠0, and d>0, characteristic zero gives (d:ℂ)≠0. Their product is nonzero in the field ℂ. This contradicts q=0, whose coefficients are all zero. Therefore d cannot be positive.
5. Since d is a natural number, d=0. The displayed expansion of p then consists solely of b_0, so p=Polynomial.C (p.coeff 0), as required.

## Key steps

1. Handle the zero polynomial and expand a nonzero polynomial through its degree.
2. For positive degree d, compute the degree-(d−1) coefficient of the translation difference.
3. Show every lower-degree summand contributes zero to that coefficient.
4. Use characteristic zero and the nonzero translation to contradict invariance.
5. Recover the constant polynomial from its degree-zero coefficient.

## Reference use

### local-project

Queries:
- `BinaryForm|binaryFormRepSL|def.*T\b|unipotent|translation|homogeneous`
- `IsHomogeneous|mem_homogeneousSubmodule|coeff.*eq_zero`
- `eval₂_monomial|eval₂_eq|eval₂_X|eval₂_C`
- `theorem coe_T_zpow|theorem coe_T_pow|def T :`
- `Polynomial.*[pP]eriodic|[pP]eriodic.*Polynomial|comp_X_add_C_eq_self|eq_C_of_periodic|eq_C_of_comp|dehomogen`
- `p02_es_177ebb5a_tff_(periodic_polynomial_constant|constant_dehomogenization)`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`
- `cmp Definitions/Def_HeckeEis_BinaryFormRep.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_tff_decomposition_types.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_tff_decomposition_instances.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/Polynomial/Taylor.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/tmp/p02_tff_decomposition_types.lean`
- `/tmp/p02_tff_decomposition_instances.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Active binary-form definitions match the snapshot byte-for-byte, and local mathlib is clean at the pinned revision. BinaryForm is the homogeneous submodule, and binarySubst uses column substitution, confirming that T^N substitutes Y by NX+Y. Polynomial.taylor_coeff supplies translation-coefficient infrastructure; IsHomogeneous.coeff_eq_zero and eval₂_monomial support homogeneous reconstruction. The snapshot-wide periodicity/dehomogenization search returned no matches. Both proposed names have no matches in the current DAG, node records, or Submission.lean. Both exact child types elaborate after import Submission. Explicit elaboration confirms Polynomial.instAdd, Polynomial.commSemiring, and the AddMonoidAlgebra multiplication and power instances underlying MvPolynomial. Transitive axiom checks for binaryFormRepSL_apply_coe, coe_T_zpow, taylor_coeff, IsHomogeneous.coeff_eq_zero, and eval₂_monomial report only propext, Classical.choice, and Quot.sound. These are interface and reference checks, not comparator acceptance of new proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/193

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
