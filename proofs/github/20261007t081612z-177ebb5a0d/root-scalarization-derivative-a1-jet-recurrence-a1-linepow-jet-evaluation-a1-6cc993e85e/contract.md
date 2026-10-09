<!-- theorem-id: fermat-p02/root.scalarization_derivative-a1.jet_recurrence-a1.linepow_jet_evaluation-a1 -->

## Theorem `Submission.p02_es_177ebb5a_sd_jr_linepow_eval`

For natural numbers n,r with r≤n and any t∈ℂ, let D_Y denote formal differentiation in variable 1. The evaluation of D_Y^r(linePow n t) at (1,−t) equals n! when r=n and equals zero otherwise.

Node: `root.scalarization_derivative-a1.jet_recurrence-a1.linepow_jet_evaluation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/68

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_sd_jr_linepow_eval`

```lean
∀ (n r : ℕ), r ≤ n → ∀ t : ℂ, MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] (HeckeEis.linePow n t).val) = (if r = n then (Nat.factorial n : ℂ) else 0)
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

- Parent DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1`
- Child DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1.linepow_jet_evaluation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n,r with r≤n and t∈ℂ. Write X=X_0, Y=X_1, D=D_Y, and L=C(t)X+Y. By the definition of linePow, its underlying polynomial is L^n.
2. Formal differentiation kills C(t) and X and sends Y to 1. The product and sum rules therefore give D(L)=1.
3. For 0≤s≤n, define A(n,s) to be the complex number obtained from the integer product n(n−1)⋯(n−s+1), with A(n,0)=1. We prove D^s(L^n)=C(A(n,s))L^(n−s) by induction on s up to n. At s=0 this is the identity L^n=L^n. If s<n and the formula holds at s, linearity over constants and the power rule give D^(s+1)(L^n)=C(A(n,s))·(n−s)L^(n−s−1)D(L). By step 2, D(L)=1; the coefficient is A(n,s+1)=A(n,s)(n−s), and n−s−1=n−(s+1). This proves the induction step.
4. Evaluation at X=1 and Y=−t sends L to t−t=0. Applying this ring homomorphism to the formula at s=r gives A(n,r)·0^(n−r).
5. If r≠n, then r≤n implies r<n, so n−r>0. Thus the value in step 4 is zero.
6. If r=n, the exponent in step 4 is zero and its power is 1. The descending product A(n,n) equals (n!:ℂ): for n=0 both are 1, and for n+1 the descending product is (n+1) times the product for n, exactly the factorial recursion. Hence the value is n!, proving the stated conditional formula, including n=r=0.

## Key steps

1. Identify linePow n t with (C(t)X+Y)^n.
2. Compute D_Y(C(t)X+Y)=1.
3. Inductively obtain the falling-factorial formula for each partial derivative.
4. Evaluate the linear factor to zero at (1,−t).
5. Separate r<n from r=n and identify the endpoint product with n!.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|linePow|jet_recurrence|iterate.*pderiv|pderiv.*iterate`
- `pderiv|iterate|eval.*deriv|deriv.*eval`
- `jet|pderiv|falling|descFactorial|linepow.*eval|linePow.*eval`
- `isHomogeneous_iff|def IsHomogeneous|homogeneousSubmodule|coeff.*degree`
- `hasDerivAt_sum|HasDerivAt.sum|HasDerivAt.mul|HasDerivAt.pow|HasDerivAt.neg`
- `ofComplex_apply`
- `p02_es_177ebb5a_sd_jr_`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_es_177ebb5a_sd_jr_child_types.lean`
- `python3 /tmp/p02_es_177ebb5a_sd_jr_reference_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/PDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/tmp/p02_es_177ebb5a_sd_jr_child_types.lean`
- `/tmp/p02_es_177ebb5a_sd_jr_reference_check.py`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous polynomial submodule; IsEichlerIntegral supplies coefficientwise HasDerivAt hypotheses; linePow has underlying polynomial (C t * X 0 + X 1)^n. The inspected mathlib files supply coefficient vanishing by homogeneity, formal monomial and power differentiation, finite-sum/product/power differentiation, and UpperHalfPlane.ofComplex_apply. No matching jet recurrence or iterated-partial evaluation result was found in the searched P2M directory. All three proposed types elaborated after import Submission under Lean 4.33.1. Their polynomial carriers are explicitly MvPolynomial (Fin 2) ℂ; no constructed matrix or ambiguous function multiplication occurs. The proposed identifiers were absent from the searched declarations and DAG metadata. Installed dependencies matched their pinned revisions with clean tracked sources, and the inspected definition and mathematical source files matched the snapshot. Transitive axiom checks of the cited library lemmas returned only propext, Classical.choice, and Quot.sound. These are interface and reference checks, not comparator acceptance of the proposed children.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/183

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
