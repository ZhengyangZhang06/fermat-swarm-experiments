# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1`
- Child DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1.homogeneous_nilpotence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n and P. Write X=X_0, Y=X_1, and D=D_Y. Membership in BinaryForm ℂ n says that every exponent vector d with nonzero coefficient in P has total degree n. Since there are exactly two variables, this means d(0)+d(1)=n.
2. For each k with 0≤k≤n, let d_k have coordinates d_k(0)=n−k and d_k(1)=k, and let a_k=coeff d_k P. Every exponent vector from step 1 is uniquely d_k with k=d(1). The finite monomial expansion of P therefore gives P=Σ_{k=0}^n C(a_k)X^(n−k)Y^k.
3. Formal differentiation is ℂ-linear, kills constants and X, and sends Y to 1. Consequently, for any a∈ℂ and natural u,v, D(C(a)X^uY^v)=v C(a)X^uY^(v−1) when v>0, and it is zero when v=0. This follows directly from the product rule and the power rule.
4. Fix k≤n. Induction on s≤k using step 3 gives D^s(C(a_k)X^(n−k)Y^k)=[k(k−1)⋯(k−s+1)] C(a_k)X^(n−k)Y^(k−s), where the product for s=0 is 1. At s=k this polynomial contains no Y, so its next derivative is zero. Every subsequent derivative remains zero. Since n+1≥k+1, the (n+1)-st derivative of this summand is zero.
5. Iterating a linear map preserves additivity, so D^(n+1) distributes over the finite sum in step 2. Every summand vanishes by step 4; hence D^(n+1)P=0. This also covers n=0, when P is constant.

## Key steps

1. Use homogeneity to restrict exponents to d(0)+d(1)=n.
2. Expand P on the finite monomial family X^(n−k)Y^k.
3. Compute repeated Y-partials of each monomial by induction.
4. Each summand vanishes after at most n+1 derivatives.
5. Distribute the iterated linear operator over the finite sum.

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
