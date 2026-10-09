<!-- theorem-id: fermat-p02/root.primitive_exists-a1.holomorphic_integral-a1.prescribed_binary_coefficients-a1 -->

## Theorem `Submission.p02_es_177ebb5a_hi_prescribed_coefficients`

For every natural number n and every function a : ℕ → ℂ, there exists P ∈ BinaryForm ℂ n such that, for every exponent index d : Fin 2 →₀ ℕ, coeff d P equals a(d(0)) when d(0)+d(1)=n, and equals zero otherwise.

Node: `root.primitive_exists-a1.holomorphic_integral-a1.prescribed_binary_coefficients-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/38

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_hi_prescribed_coefficients`

```lean
∀ (n : ℕ) (a : ℕ → ℂ), ∃ P : ↥(HeckeEis.BinaryForm ℂ n), ∀ d : Fin 2 →₀ ℕ, MvPolynomial.coeff d P.val = if d 0 + d 1 = n then a (d 0) else 0
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

- Parent DAG node: `root.primitive_exists-a1.holomorphic_integral-a1`
- Child DAG node: `root.primitive_exists-a1.holomorphic_integral-a1.prescribed_binary_coefficients-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n and a. For every integer r with 0≤r≤n, define e_r=Finsupp.single 0 r+Finsupp.single 1 (n−r). Since 0 and 1 are distinct and exhaust Fin 2, e_r(0)=r, e_r(1)=n−r, and the total degree of e_r is r+(n−r)=n.
2. Define the polynomial P₀=Σ_{r=0}^n monomial e_r (a(r)) in MvPolynomial (Fin 2) ℂ. Each summand is homogeneous of degree n because its exponent index has degree n; this remains true when its scalar coefficient vanishes. A finite sum of homogeneous polynomials of the same degree is homogeneous of that degree. Thus P₀ determines an element P of BinaryForm ℂ n.
3. Fix an arbitrary exponent index d. Coefficients commute with finite sums, and the d coefficient of monomial e_r (a(r)) is a(r) if d=e_r and zero otherwise. Consequently coeff d P is the sum of a(r) over precisely those r∈{0,…,n} for which d=e_r.
4. Suppose d(0)+d(1)=n. Set r=d(0). Nonnegativity of d(1) gives r≤n, and the equality gives n−r=d(1). Therefore e_r and d agree at both elements of Fin 2, so e_r=d. If e_s=d for another s∈{0,…,n}, evaluation at 0 gives s=d(0)=r. There is exactly one contributing term in the coefficient sum, and its value is a(d(0)).
5. Suppose instead d(0)+d(1)≠n. Equality d=e_r for any r∈{0,…,n} would imply d(0)+d(1)=r+(n−r)=n, a contradiction. Every term in the coefficient sum is therefore zero. The two cases establish the required formula for every d and complete the construction of P.

## Key steps

1. Construct exponent indices e_r with entries r and n−r and verify their degree is n.
2. Sum monomials with coefficients a(r) and use homogeneity to obtain a binary form.
3. Express each coefficient as a finite sum of matching monomial coefficients.
4. Identify the unique matching index r=d(0) when d(0)+d(1)=n.
5. Show no index matches when d(0)+d(1)≠n.

## Reference use

### local-project

Queries:
- `def (BinaryForm|linePow|IsEichlerIntegral)|theorem.*(linePow|coeff)|IsHomogeneous`
- `coeff.*(add.*pow|X.*pow)|IsHomogeneous.coeff_eq_zero|isHomogeneous_monomial|coe_ofComplex|ofComplex_coe`
- `^((noncomputable )?(def|abbrev|theorem|lemma)) .*linePow.*coeff|^((noncomputable )?(def|abbrev|theorem|lemma)) .*coeff.*linePow`
- `p02_es_177ebb5a_hi_(prescribed_coefficients|linepow_coefficients)`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_177ebb5a_hi_decomposition_types.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Coeff.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-scalar-primitive-a1/comparator-v2-integration-repair-1.log`
- `/tmp/p02_177ebb5a_hi_decomposition_types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous submodule; linePow has underlying polynomial (C z * X 0 + X 1)^n; IsEichlerIntegral is exactly the coefficientwise derivative predicate. Homogeneous.lean supplies homogeneous monomials and finite sums. Coeff.lean supplies coeff_linearCombination_X_pow_of_fintype; no named specialized linePow coefficient theorem was found in the pinned project. Topology.lean supplies eventuallyEq_coe_comp_ofComplex. The inspected dependency files match the snapshot, and mathlib is clean at its pinned revision. Both proposed types elaborate after import Submission, with the final check exiting successfully. Audited library declarations use only propext, Classical.choice, and Quot.sound. Neither proposed name occurs in the inspected DAG. The inherited scalar-primitive node is marked proved and its recorded comparator reports acceptance with only those standard axioms.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/220

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
