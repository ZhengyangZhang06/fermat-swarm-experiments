<!-- theorem-id: fermat-p02/root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.finite_jet_sum_derivative-a1 -->

## Theorem `Submission.p02_es_177ebb5a_med_sum_derivative`

Let n,r∈ℕ, a:Fin(n+1)→ℂ→ℂ, b:Fin(n+1)→ℂ and c,t∈ℂ. Assume that for every k∈Fin(n+1), a k has complex derivative c·b k at t. Define A(m,s)=(Nat.descFactorial m s : ℂ), with A(m,0)=1 and A(m,s+1)=A(m,s)·(m−s), using natural subtraction before casting. Then z↦Σ_k a k z·A(k.val,r)·(−z)^(k.val−r) has complex derivative c·Σ_k b k·A(k.val,r)·(−t)^(k.val−r) − Σ_k a k t·A(k.val,r+1)·(−t)^(k.val−(r+1)) at t. Every sum is over Fin(n+1), and every exponent subtraction is natural subtraction.

Node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.finite_jet_sum_derivative-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/85

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_med_sum_derivative`

```lean
∀ (n r : ℕ) (a : Fin (n + 1) → ℂ → ℂ) (b : Fin (n + 1) → ℂ) (c t : ℂ), (∀ k : Fin (n + 1), HasDerivAt (a k) (c * b k) t) → HasDerivAt (fun z : ℂ => ∑ k : Fin (n + 1), a k z * (Nat.descFactorial k.val r : ℂ) * (-z) ^ (k.val - r)) (c * (∑ k : Fin (n + 1), b k * (Nat.descFactorial k.val r : ℂ) * (-t) ^ (k.val - r)) - (∑ k : Fin (n + 1), a k t * (Nat.descFactorial k.val (r + 1) : ℂ) * (-t) ^ (k.val - (r + 1)))) t
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

- Parent DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1`
- Child DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.finite_jet_sum_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n,r,a,b,c,t and assume HasDerivAt (a k) (c b k) t for every k∈Fin(n+1). For a fixed k put m=k.val and A_s=(Nat.descFactorial m s : ℂ). Its defining recurrence is A_(r+1)=A_r·(m−r), where m−r is natural subtraction cast to ℂ.
2. Set q=m−r. The function z↦−z has derivative −1 at t. If q=0, its q-th power is the constant 1 with derivative zero; the formula −(q:ℂ)(−t)^(q−1) is also zero. If q>0, the power and chain rules give precisely that same derivative. Thus the formula holds for every q, including t=0.
3. Multiplying the coefficient derivative by the constant A_r and applying the product rule with this power function shows that z↦a k z·A_r·(−z)^q has derivative (c b k)·A_r·(−t)^q − a k t·A_r·(q:ℂ)·(−t)^(q−1) at t.
4. Natural subtraction gives q−1=(m−r)−1=m−(r+1). By the recurrence in step 1, A_r·(q:ℂ)=A_(r+1). Consequently the derivative in step 3 is c·(b k·A_r·(−t)^(m−r)) − a k t·A_(r+1)·(−t)^(m−(r+1)). When m≤r, q=0 and A_(r+1)=0, so this calculation also accounts for every vanished power-derivative term.
5. Apply the finite-sum derivative rule over Fin(n+1). Sum the first derivative contribution and factor out c; sum the second contribution and use distribution of subtraction over a finite sum. The result is exactly the stated derivative. Only derivatives at t have been used, so no additional regularity hypothesis is needed.

## Key steps

1. Differentiate each negative power, treating exponent zero explicitly.
2. Apply constant multiplication and the product rule to each summand.
3. Use the falling-factorial recurrence and natural-subtraction identity to identify the next-order term.
4. Sum the derivatives and factor out c.

## Reference use

### local-project

Queries:
- `homogeneous_nilpotence|def BinaryForm|abbrev BinaryForm|theorem.*(pderiv|coeff|deriv)|lemma.*(pderiv|coeff|deriv)`
- `coeff_pderiv|pderiv_monomial|pderiv_pow`
- `descFactorial.*(succ|eq_zero)|descFactorial_succ|def descFactorial`
- `support_sum_monomial_coeff|eval_monomial|def IsHomogeneous|mem_homogeneousSubmodule`
- `theorem.*(sum|pow|mul_const)|lemma.*(sum|pow|mul_const)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/PDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Nat/Factorial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous-polynomial submodule. The snapshot supplies support_sum_monomial_coeff, eval_monomial, pderiv_monomial, the descFactorial recurrence, and finite-sum/product/power derivative rules. No homogeneous_nilpotence match was found in the pinned project. Installed mathlib is clean at the pinned revision; the inspected differentiation and factorial sources match the snapshot. Both proposed types successfully elaborated after import Submission using Lean 4.33.1. Axiom checks of support_sum_monomial_coeff, pderiv_monomial, HasDerivAt.fun_sum, HasDerivAt.mul and HasDerivAt.pow reported only propext, Classical.choice and Quot.sound; descFactorial_succ uses no axioms. These are interface and supporting-library checks, not acceptance of unimplemented child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/216

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
