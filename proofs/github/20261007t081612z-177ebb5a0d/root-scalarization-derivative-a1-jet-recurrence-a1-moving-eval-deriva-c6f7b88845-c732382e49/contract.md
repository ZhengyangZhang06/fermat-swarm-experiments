<!-- theorem-id: fermat-p02/root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.binary_form_jet_expansion-a1.iterated_binary_monomial_pderiv-a1 -->

## Theorem `Submission.p02_es_177ebb5a_med_js_iterated_monomial`

For every exponent d:Fin 2→₀ℕ, coefficient a∈ℂ, and r∈ℕ, let D be formal differentiation in variable 1 on MvPolynomial (Fin 2) ℂ. Then D iterated r times on monomial d a equals monomial (d−single 1 r) (a·(Nat.descFactorial (d(1)) r : ℂ)). Subtraction of exponent vectors is coordinatewise natural subtraction. There is no restriction on r or d.

Node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.binary_form_jet_expansion-a1.iterated_binary_monomial_pderiv-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/177

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_med_js_iterated_monomial`

```lean
∀ (d : Fin 2 →₀ ℕ) (a : ℂ) (r : ℕ), ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] (MvPolynomial.monomial d a)) = MvPolynomial.monomial (d - Finsupp.single (1 : Fin 2) r) (a * (Nat.descFactorial (d 1) r : ℂ))
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

- Parent DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.binary_form_jet_expansion-a1`
- Child DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.binary_form_jet_expansion-a1.iterated_binary_monomial_pderiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix d:Fin 2→₀ℕ and a∈ℂ. Put D=∂/∂X₁, δ_s=d−single 1 s, and A_s=(Nat.descFactorial (d(1)) s : ℂ). Coordinatewise natural subtraction gives δ_s(0)=d(0) and δ_s(1)=d(1)−s. The descending-factorial recurrence, after casting and commuting the factors, is A_{s+1}=A_s·((d(1)−s : ℕ) : ℂ).
2. For any exponent e and b∈ℂ, one differentiation gives D(monomial e b)=monomial (e−single 1 1) (b·(e(1):ℂ)). Indeed, monomial e b is C(b)X₀^{e(0)}X₁^{e(1)}; D annihilates C(b) and X₀, and differentiating X₁^{e(1)} multiplies by e(1) and lowers that exponent by one. When e(1)=0 the derivative and the displayed monomial both vanish, because the latter has coefficient zero. Thus this identity includes the zero-exponent case.
3. We prove the claimed formula by induction on s. For s=0, the iterate is the identity, δ_0=d, and A_0=1. Consequently D^0(monomial d a)=monomial δ_0 (a·A_0).
4. Assume D^s(monomial d a)=monomial δ_s (a·A_s). Apply D to this equality and use step 2. The result is monomial (δ_s−single 1 1) ((a·A_s)·((d(1)−s : ℕ):ℂ)). At coordinate 0, δ_s−single 1 1 has value d(0). At coordinate 1, it has value (d(1)−s)−1=d(1)−(s+1), by associativity of natural subtraction. Since these are all coordinates, δ_s−single 1 1=δ_{s+1}.
5. By the recurrence in step 1 and associativity of complex multiplication, the coefficient obtained in step 4 is a·A_{s+1}. This proves the induction step and hence the formula for every r∈ℕ. In particular, whenever d(1)≤s, the factor d(1)−s is zero, so the successor derivative and the asserted successor monomial both vanish. No bound on the derivative order was used.

## Key steps

1. Compute the coordinates of the truncated exponent and the cast descending-factorial recurrence.
2. Establish the one-step monomial derivative formula, including exponent zero.
3. Verify the zeroth iterate.
4. Apply one differentiation to the induction hypothesis and identify the successor exponent coordinatewise.
5. Use the factorial recurrence to identify the successor coefficient, including orders beyond the original exponent.

## Reference use

### local-project

Queries:
- `BinaryForm|pderiv|descFactorial|sum_monomial`
- `descFactorial_succ|descFactorial_zero|iterate.*pderiv|pderiv.*iterate`
- `coeff_eq_zero`
- `iterate.*pderiv|pderiv.*iterate|descFactorial`
- `p02_es_177ebb5a_med_js_iterated_monomial`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_med_jet_split_typecheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/PDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Nat/Factorial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1-linear-coeff-derivative-a-ef3717e3c5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1-linear-coeff-derivative-a-ef3717e3c5/lean-audit-v1.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1-linear-coeff-derivative-a-ef3717e3c5/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1-linear-coeff-derivative-a-ef3717e3c5/comparator-v1-integration.log`
- `/tmp/p02_med_jet_split_typecheck.lean`

The snapshot pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous polynomial submodule. The inspected library supplies off-degree coefficient vanishing, pderiv_monomial, and the descending-factorial recurrence with natural subtraction; the MvPolynomial search found no iterated-pderiv descending-factorial formula. The existing expansion has an identical frozen type, passing exact-contract and integration comparators, and an accepted independent review; its transitive axioms are only propext, Classical.choice, and Quot.sound. It is present in this parent's frozen base. All nine installed dependencies are clean and match their pins, and the three directly imported project definitions byte-match the snapshot. Both proposed types successfully elaborated after import Submission using Lean 4.33.1. Instance checks returned AddMonoidAlgebra.algebra.toSMul and Finsupp.tsub, as intended. The new identifier has no match in Submission.lean or the current DAG.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/198

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
