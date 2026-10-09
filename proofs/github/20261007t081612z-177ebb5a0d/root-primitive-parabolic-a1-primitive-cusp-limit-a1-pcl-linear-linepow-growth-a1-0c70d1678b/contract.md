<!-- theorem-id: fermat-p02/root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_linear_linepow_growth-a1 -->

## Theorem `Submission.p02_es_177ebb5a_pcl_linear_linepow_growth`

For every natural number n and every complex-linear map T:BinaryForm ℂ n→BinaryForm ℂ n, there exists a real K≥0 such that, for every z∈ℂ and every monomial exponent d, |coeff_d(T((zX+Y)^n))|≤K(1+|z|)^n. The same K works for all z and all d.

Node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_linear_linepow_growth-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/71

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_pcl_linear_linepow_growth`

```lean
∀ (n : ℕ) (T : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n)), ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (d : Fin 2 →₀ ℕ), ‖MvPolynomial.coeff d (T (HeckeEis.linePow n z)).val‖ ≤ K * (1 + ‖z‖) ^ n
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

- Parent DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1`
- Child DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_linear_linepow_growth-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n and T. For each integer r with 0≤r≤n, let b_r=X^rY^(n−r), regarded as a binary form of degree n. This membership holds because its only monomial has total degree r+(n−r)=n. Write Q_r=T(b_r).
2. Define k_r to be the sum of |coeff_e(Q_r)| over the finite support of Q_r. Then k_r≥0. For every exponent d, |coeff_d(Q_r)|≤k_r: if d belongs to the support, its nonnegative summand is bounded by the whole sum; otherwise its coefficient is zero.
3. Define K=Σ_{r=0}^n binomial(n,r)k_r, with the binomial coefficients viewed as nonnegative real numbers. This is a finite nonnegative real number depending only on n and T.
4. The binomial theorem gives (zX+Y)^n=Σ_{r=0}^n (binomial(n,r)z^r)·b_r. Applying T and then the d-coefficient, both complex-linear, gives coeff_d(T((zX+Y)^n))=Σ_{r=0}^n binomial(n,r)z^r coeff_d(Q_r).
5. Put q=1+|z|. We have q≥1 and |z|≤q. Therefore, for every r≤n, |z|^r≤q^r≤q^n. The triangle inequality and step 2 now give |coeff_d(T((zX+Y)^n))|≤Σ_{r=0}^n binomial(n,r)|z|^r k_r≤Σ_{r=0}^n binomial(n,r)q^n k_r=Kq^n.
6. This proves the required estimate for arbitrary z and d with the single constant K. The argument includes n=0: the sum then has only r=0 and all zeroth powers equal one.

## Key steps

1. Expand the line power in the degree-n monomials.
2. Bound every coefficient of each fixed image T(b_r) by its finite sum of coefficient norms.
3. Form a nonnegative constant from these bounds and binomial coefficients.
4. Apply linearity and the triangle inequality.
5. Bound every power |z|^r by (1+|z|)^n.

## Reference use

### local-project

Queries:
- `scaled_cusp_decay|IsEichlerIntegral|binaryFormRepSL|eichlerShimuraMap_injective`
- `hasDerivAt|ofComplex|coe_specialLinearGroup_apply`
- `integrableOn.*exp|integrableOn.*rpow|tendsto.*exp.*atTop`
- `sum_monomial_eq|coeff_sum|coeff_smul|coeff_monomial|coeff_mul_X|coeff_add`
- `scaled_cusp_decay|common_ray_limit|linear_linepow_growth`
- `sed -n '35,135p' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_pcl_decomposition_checks/Check.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The installed mathlib HEAD matches and has no tracked modifications; both inspected HeckeEis definition files match the snapshot byte-for-byte. The snapshot supplies coefficientwise IsEichlerIntegral, binaryFormRepSL_linePow, jFactor_ne_zero, the local ofComplex identities, the Möbius derivative, coefficient linearity, homogeneous support, exponential asymptotics, and the fundamental theorem of calculus. Searching the snapshot for scaled_cusp_decay|common_ray_limit|linear_linepow_growth returned no matches; scaled_cusp_decay is an existing parent DAG dependency. All three proposed types elaborated after import Submission. Transitive axiom checks of binaryFormRepSL_linePow, jFactor_ne_zero, hasStrictDerivAt_smul, integral_eq_sub_of_hasDerivAt, and tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero returned only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/189

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
