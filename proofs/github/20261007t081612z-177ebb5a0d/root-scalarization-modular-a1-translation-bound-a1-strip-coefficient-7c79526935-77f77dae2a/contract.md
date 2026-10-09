<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.linepow_coefficient_bound-a1 -->

## Theorem `Submission.p02_es_177ebb5a_scl_linepow_coeff_bound`

For every n∈ℕ, z∈ℂ, and exponent d:Fin 2→₀ℕ, the coefficient of the monomial d in HeckeEis.linePow n z=(zX+Y)^n has absolute value at most 2^n(max(1,|z|))^n.

Node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.linepow_coefficient_bound-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/104

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_scl_linepow_coeff_bound`

```lean
∀ (n : ℕ) (z : ℂ) (d : Fin 2 →₀ ℕ), ‖MvPolynomial.coeff d (HeckeEis.linePow n z).val‖ ≤ (2 : ℝ) ^ n * (max 1 ‖z‖) ^ n
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

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.linepow_coefficient_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write X=X₀ and Y=X₁. By definition, (HeckeEis.linePow n z).val=(zX+Y)^n. The binomial theorem expands this as Σ_{r=0}^n binom(n,r) z^r X^r Y^(n−r).
2. Distinct indices r give distinct exponents, since their X-exponents differ. If d(0)+d(1)≠n, no summand has exponent d, so its coefficient is zero. The claimed right-hand side is nonnegative, proving this case.
3. Otherwise put r=d(0). Then r≤n and d(1)=n−r, so the coefficient is binom(n,r) z^r. Its absolute value is binom(n,r)|z|^r, regarding the nonnegative integer binomial coefficient as a real number.
4. Every binomial coefficient is at most Σ_{j=0}^n binom(n,j)=2^n, because every summand is nonnegative. Put M=max(1,|z|). Then |z|≤M and M≥1 imply |z|^r≤M^r≤M^n. Multiplying these two bounds gives the desired inequality. These arguments also cover n=0 and z=0, with the usual convention z^0=1.

## Key steps

1. Expand (zX+Y)^n by the binomial theorem.
2. Identify degree-n coefficients and show all other coefficients vanish.
3. Bound the binomial coefficient by 2^n.
4. Bound |z|^r by max(1,|z|)^n for r≤n.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|def linePow|abbrev BinaryForm|strip.*limit|coefficient.*limit`
- `integrable.*exp|tendsto.*exp|norm_sub_le_integral|finite_of_degree_eq|coeff.*pow`
- `tendsto_pow_mul_exp_neg_atTop_nhds_zero|tendsto_pow_mul_exp|finite_of_degree_eq|continuous.*coeff|ofComplex.*continuous|continuous.*ofComplex`
- `coeff_eq_zero|mem_homogeneousSubmodule|isHomogeneous_monomial|degree`
- `strip.*limit|limit.*strip|linePow.*(bound|norm)|norm.*linePow`
- `rg -n --hidden -g 'dag.json' -g 'decomposition-v*.json' -g '*handoff*.json' -g '*.lean' 'p02_es_177ebb5a_scl_(linepow_coeff_bound|polynomial_exp_tail|scalar_strip_limit)' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_scl_decomposition_types.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Coeff.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/ExpDecay.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DistLEIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Finsupp/Weight.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis`
- `/tmp/p02_scl_decomposition_types.lean`

Both reference snapshots are clean and match project revision 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib is clean at that revision, and the two relevant project definition files match the snapshot byte-for-byte. IsEichlerIntegral specifies coefficientwise complex derivatives; BinaryForm is the homogeneous polynomial submodule. Mathlib supplies multinomial coefficient formulas, exponential integrability and decay, segment norm estimates, finite degree-coordinate sets, and off-degree coefficient vanishing. The strip-limit/linePow-bound search returned no matches. All three proposed names were absent from the DAG and recorded handoffs/decompositions. All three exact types elaborate after import Submission. Transitive axiom checks for the seven inspected supporting declarations report only propext, Classical.choice, and Quot.sound. These are interface and reference checks, not comparator acceptance of any proposed child proof.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/176

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
