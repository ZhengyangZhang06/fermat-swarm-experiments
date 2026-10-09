<!-- theorem-id: fermat-p02/root.scalarization_derivative-a1.open_derivative_ladder-a1 -->

## Theorem `Submission.p02_es_177ebb5a_sd_open_ladder`

Let U⊆ℂ be open, n∈ℕ, Q : ℕ → ℂ → ℂ, and g : ℂ → ℂ. Suppose that for every r<n and z∈U, Q_r has complex derivative −Q_{r+1}(z) at z, and that for every z∈U, Q_n has complex derivative g(z) at z. Then for every z∈U, iteratedDeriv (n+1) Q_0 z = (−1)^n g(z). No assumptions are imposed outside U.

Node: `root.scalarization_derivative-a1.open_derivative_ladder-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/29

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_sd_open_ladder`

```lean
∀ (U : Set ℂ) (n : ℕ) (Q : ℕ → ℂ → ℂ) (g : ℂ → ℂ), IsOpen U → (∀ (r : ℕ), r < n → ∀ z ∈ U, HasDerivAt (Q r) (-Q (r + 1) z) z) → (∀ z ∈ U, HasDerivAt (Q n) (g z) z) → ∀ z ∈ U, iteratedDeriv (n + 1) (Q 0) z = (-1 : ℂ) ^ n * g z
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
- Child DAG node: `root.scalarization_derivative-a1.open_derivative_ladder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix U, n, Q, g, and the stated hypotheses. We prove by induction on r≤n that iteratedDeriv r (Q 0) z=(−1)^r Q_r(z) for every z∈U. At r=0, the zeroth iterated derivative is Q_0 and (−1)^0=1, so the identity holds.
2. Suppose the identity holds at r and r+1≤n. Fix z∈U. Because U is open, it is a neighborhood of z, and the induction hypothesis shows that the functions iteratedDeriv r (Q 0) and w↦(−1)^r Q_r(w) agree on this neighborhood. The recurrence hypothesis applies because r<n. Multiplying its derivative by the constant (−1)^r shows that the second function has derivative (−1)^r(−Q_{r+1}(z)) at z. Neighborhood equality transfers this HasDerivAt statement to the first function. Therefore, using iteratedDeriv_succ, iteratedDeriv (r+1) (Q 0) z=(−1)^r(−Q_{r+1}(z))=(−1)^{r+1}Q_{r+1}(z). This proves the induction step simultaneously at every point of U.
3. The induction gives iteratedDeriv n (Q 0)=(w↦(−1)^n Q_n(w)) on U. Fix z∈U once more. Openness turns this equality into neighborhood equality at z. The terminal derivative hypothesis and constant multiplication give derivative (−1)^n g(z) for the right-hand function. Transfer this derivative through neighborhood equality and apply iteratedDeriv_succ to obtain iteratedDeriv (n+1) (Q 0) z=(−1)^n g(z).
4. The point z was arbitrary in U, proving the conclusion. For n=0 the induction uses only its base case and the terminal derivative hypothesis, so the argument includes that case. Every transfer of derivatives used a neighborhood contained in U; hence no behavior outside U was assumed.

## Key steps

1. Inductively identify the r-th iterated derivative with (−1)^r Q_r on U for r≤n.
2. Use openness to transfer derivatives across the neighborhood equality at each induction step.
3. Apply the terminal derivative of Q_n to the identity at r=n.
4. Use iteratedDeriv_succ to obtain the required derivative of order n+1, including n=0.

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

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/159

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
