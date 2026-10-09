<!-- theorem-id: fermat-p02/root.scalarization_derivative-a1.jet_recurrence-a1 -->

## Theorem `Submission.p02_es_177ebb5a_sd_jet_recurrence`

Let n be a natural number, h : ℍ → ℂ, and E : ℍ → BinaryForm ℂ n satisfy HeckeEis.IsEichlerIntegral n h E. Write D_Y for formal polynomial differentiation in variable 1, and define Q_r(z)=(D_Y^r(E(ofComplex z)))(1,−z) for every natural r and complex z. For every r≤n and τ∈ℍ, Q_r has complex derivative at τ equal to n!h(τ) if r=n, and equal to −Q_{r+1}(τ) otherwise.

Node: `root.scalarization_derivative-a1.jet_recurrence-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/29

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/83, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/84, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/85

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_sd_jet_recurrence`

```lean
∀ (n : ℕ) (h : UpperHalfPlane → ℂ) (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n h E → ∀ (r : ℕ), r ≤ n → ∀ τ : UpperHalfPlane, HasDerivAt (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] (E (UpperHalfPlane.ofComplex z)).val)) (if r = n then (Nat.factorial n : ℂ) * h τ else -MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r + 1] (E τ).val)) (τ : ℂ)
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

- Parent DAG node: `root.scalarization_derivative-a1`
- Child DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, h, E, and the hypothesis IsEichlerIntegral n h E. Write X=X_0 and Y=X_1. For 0≤k≤n, let d_k be the exponent vector with d_k(0)=n−k and d_k(1)=k, and define a_k(z)=coeff d_k (E(ofComplex z)). Every nonzero coefficient of this homogeneous polynomial has total degree n. An exponent vector in two variables of total degree n is uniquely d_k for k equal to its exponent of Y. Consequently, for every complex z, E(ofComplex z)=Σ_{k=0}^n a_k(z)X^{n−k}Y^k. This identity uses the same finite index set for every z.
2. For 0≤r≤k define c(k,r)=k(k−1)⋯(k−r+1), with c(k,0)=1, regarding these integers as complex numbers. Repeated formal differentiation gives D_Y^r(X^{n−k}Y^k)=c(k,r)X^{n−k}Y^{k−r} when r≤k, and gives zero when r>k. Indeed, the r=0 identity is immediate; differentiating a term with r<k multiplies its coefficient by k−r and lowers its Y-exponent by one, whereas differentiating at r=k gives zero. Subsequent derivatives of zero remain zero. By linearity and evaluation at (1,−z), it follows that Q_r(z)=Σ_{k=r}^n a_k(z)c(k,r)(−z)^{k−r} for r≤n, and Q_{n+1}(z)=0 for every z.
3. Fix r≤n and τ∈ℍ, and put t=(τ:ℂ). Let L=tX+Y and b_k=coeff d_k (L^n). The defining IsEichlerIntegral hypothesis, applied to d_k and τ, says that a_k has complex derivative h(τ)b_k at t. Also ofComplex t=τ. Since linePow n t has underlying polynomial L^n, and L^n is homogeneous of degree n, its expansion on the same index set is Σ_{k=0}^n b_k X^{n−k}Y^k.
4. Differentiate the finite expression for Q_r at t using these coefficient derivatives and the product rule. Differentiating the coefficients contributes h(τ)Σ_{k=r}^n b_k c(k,r)(−t)^{k−r}=h(τ)(D_Y^r L^n)(1,−t), by the expansion in step 3 and the monomial formula in step 2. The term k=r has a constant power of −z, so its substitution derivative is zero. For each k>r, differentiating that power contributes −a_k(t)c(k,r)(k−r)(−t)^{k−r−1}. Since c(k,r)(k−r)=c(k,r+1), the sum of these contributions is −Q_{r+1}(t). This also holds when r=n: the sum is empty and Q_{n+1}=0. We have thus proved HasDerivAt Q_r [h(τ)(D_Y^r L^n)(1,−t)−Q_{r+1}(t)] t.
5. The polynomial L satisfies D_Y L=1. The formal power rule and induction on r≤n therefore give D_Y^r L^n=c(n,r)L^{n−r}. The induction starts with r=0; when r<n, the next derivative multiplies by n−r, which changes c(n,r) into c(n,r+1). Since L(1,−t)=0, its evaluated r-th partial derivative is zero for r<n. For r=n the remaining power is L^0=1 and c(n,n)=n(n−1)⋯1=n!, including the empty product 0!=1.
6. If r=n, steps 4 and 5 and Q_{n+1}=0 give derivative n!h(τ). If r≠n, the assumption r≤n implies r<n, so those steps give derivative −Q_{r+1}(t). Finally, ofComplex t=τ identifies Q_{r+1}(t) with the evaluation of D_Y^{r+1}(E τ) appearing in the Lean statement. When n=0 only the first case occurs and yields derivative h(τ), as required.

## Key steps

1. Expand every homogeneous binary form on the fixed monomial set X^{n−k}Y^k.
2. Compute repeated Y-partial derivatives using falling factorials and deduce Q_{n+1}=0.
3. Extract each coefficient derivative directly from IsEichlerIntegral.
4. Differentiate the finite evaluated sum to obtain the coefficient contribution minus Q_{r+1}.
5. Evaluate D_Y^r(tX+Y)^n at (1,−t), obtaining zero below n and n! at n.
6. Separate the endpoint and lower-order cases and identify ofComplex(τ) with τ.

## Reference use

### local-project

Queries:
- `rg -n 'IsEichlerIntegral|iteratedDeriv_succ|eichler.*[Dd]eriv|partial.*[Yy]|pderiv' project/Definitions/Def_HeckeEis_EichlerIntegral.lean project/Definitions/Def_HeckeEis_BinaryFormRep.lean project/P2M mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`
- `rg -n 'scalarization|iteratedDeriv.*Eichler|Eichler.*iteratedDeriv|Q_r|pderiv' project/P2M project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `rg -n 'def pderiv|pderiv_pow|pderiv_monomial|pderiv_C|pderiv_X|iterate.*pderiv|pderiv.*iterate|pderiv_eq_zero' mathlib/Mathlib/Algebra/MvPolynomial mathlib/Mathlib/Analysis/Calculus`
- `rg -n 'ofComplex|coe_mk|coe_ofComplex' mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `rg -n 'theorem HasDerivAt.congr_of_eventuallyEq|theorem HasDerivAt.const_mul|theorem HasDerivAt.sum|hasDerivAt_sum|EventuallyEq.deriv_eq' mathlib/Mathlib/Analysis/Calculus/Deriv`
- `rg -n 'p02_es_177ebb5a_sd_jet_recurrence|p02_es_177ebb5a_sd_open_ladder' Submission.lean Definitions .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes -g '*.json' -g '*.lean'`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_es_177ebb5a_sd_child_types.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/PDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Logic/Function/Iterate.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/tmp/p02_es_177ebb5a_sd_child_types.lean`

The snapshot pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous polynomial submodule, and IsEichlerIntegral supplies precisely the required coefficientwise HasDerivAt hypotheses. PDeriv supplies monomial, power, and coefficient differentiation identities; the calculus files supply finite-sum differentiation, constant multiplication, derivative locality, and iteratedDeriv_succ. UpperHalfPlane.ofComplex_apply identifies the extension at upper-half-plane points. No matching scalarization recurrence was found in the searched P2M directory or EichlerIntegral definition file. Neither proposed identifier matched the current declarations or DAG metadata. Both final Lean types elaborated successfully after only import Submission under Lean 4.33.1. All installed dependencies matched their pinned revisions with clean tracked sources, and the checked definition and calculus files matched the snapshot. Axiom checks of the cited polynomial and calculus lemmas returned only propext, Classical.choice, and Quot.sound. These checks establish interface compatibility, not comparator acceptance of the proposed children.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
