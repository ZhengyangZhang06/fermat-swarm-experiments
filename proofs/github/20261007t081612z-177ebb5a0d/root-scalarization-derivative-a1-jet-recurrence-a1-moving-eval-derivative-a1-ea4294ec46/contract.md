<!-- theorem-id: fermat-p02/root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1 -->

## Theorem `Submission.p02_es_177ebb5a_sd_jr_moving_eval_derivative`

Let n∈ℕ, F : ℂ → BinaryForm ℂ n, G : BinaryForm ℂ n, and c,t∈ℂ. Assume that for every exponent vector d : Fin 2 →₀ ℕ, the function z↦coeff d (F z) has complex derivative c·coeff d G at t. Write D_Y for formal differentiation in variable 1. For every r≤n, the function z↦(D_Y^r(F z))(1,−z) has complex derivative c·(D_Y^r G)(1,−t)−(D_Y^(r+1)(F t))(1,−t) at t.

Node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/68

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/83

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/177, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/178

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_sd_jr_moving_eval_derivative`

```lean
∀ (n : ℕ) (F : ℂ → ↥(HeckeEis.BinaryForm ℂ n)) (G : ↥(HeckeEis.BinaryForm ℂ n)) (c t : ℂ), (∀ d : Fin 2 →₀ ℕ, HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F z).val) (c * MvPolynomial.coeff d G.val) t) → ∀ r : ℕ, r ≤ n → HasDerivAt (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] (F z).val)) (c * MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] G.val) - MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r + 1] (F t).val)) t
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
- Child DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n,F,G,c,t and the stated coefficient derivative hypothesis. Write X=X_0, Y=X_1, and D=D_Y. For 0≤k≤n define d_k by d_k(0)=n−k and d_k(1)=k, and put a_k(z)=coeff d_k(F z) and b_k=coeff d_k G. Homogeneity implies that every nonzero coefficient of F z or G has an exponent vector d with d(0)+d(1)=n. Such a vector is uniquely d_k for k=d(1). Thus, for every z, F z=Σ_{k=0}^n C(a_k(z))X^(n−k)Y^k, and G=Σ_{k=0}^n C(b_k)X^(n−k)Y^k. The index set is independent of z.
2. For 0≤s≤k let A(k,s)=k(k−1)⋯(k−s+1), interpreted in ℂ, with A(k,0)=1. Induction gives D^s(X^(n−k)Y^k)=C(A(k,s))X^(n−k)Y^(k−s). Indeed, s=0 is immediate, and when s<k differentiation multiplies by k−s and lowers the Y-exponent by one. At s=k the result has no Y, so its next derivative is zero, and all later derivatives remain zero. Linearity gives the corresponding formulas with the constant coefficients a_k(z) or b_k included.
3. Fix r≤n and define Q_r(z)=(D^r(F z))(1,−z). Applying step 2 to the expansions in step 1 and evaluating X=1,Y=−z gives Q_r(z)=Σ_{k=r}^n a_k(z)A(k,r)(−z)^(k−r). Applying the same calculation to G at (1,−t) gives (D^r G)(1,−t)=Σ_{k=r}^n b_k A(k,r)(−t)^(k−r). Here each sum is over the finite set of natural k satisfying the displayed bounds.
4. The hypothesis applied to d_k gives HasDerivAt a_k (c b_k) t. The function z↦(−z)^(k−r) is complex differentiable. If k=r, it is the constant 1 and its derivative is zero. If k>r, the derivative at t is −(k−r)(−t)^(k−r−1), by the power rule and the derivative −1 of z↦−z.
5. Apply the product rule to each summand of Q_r and then the finite-sum derivative rule. The coefficient derivatives contribute c Σ_{k=r}^n b_k A(k,r)(−t)^(k−r)=c(D^r G)(1,−t). The derivatives of the powers contribute −Σ_{k=r+1}^n a_k(t)A(k,r)(k−r)(−t)^(k−r−1).
6. If r<n, then A(k,r)(k−r)=A(k,r+1) for every index in the latter sum. Also k−r−1=k−(r+1). The monomial calculation of step 2 therefore identifies that sum with (D^(r+1)(F t))(1,−t). If r=n, the sum is empty and equals zero; homogeneous_nilpotence applied to the degree-n form F t gives D^(n+1)(F t)=0, so its evaluation is also zero. Thus in both cases the power-derivative contribution is −(D^(r+1)(F t))(1,−t).
7. Combining steps 5 and 6 yields HasDerivAt Q_r [c(D^r G)(1,−t)−(D^(r+1)(F t))(1,−t)] t, exactly the claimed derivative. No differentiability away from t was used; when n=0 the same argument uses only the constant-power and nilpotence cases.

## Key steps

1. Expand F z and G on one fixed finite homogeneous monomial family.
2. Compute iterated Y-partials of the monomials using falling factorials.
3. Express the evaluated jets as finite sums.
4. Use the coefficient hypotheses and differentiate the moving powers.
5. Identify coefficient contributions with c times the evaluated jet of G.
6. Identify substitution contributions with the negative next jet, using nilpotence at r=n.
7. Combine the two contributions into the stated HasDerivAt conclusion.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/429

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
