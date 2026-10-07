# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1.translation_fixed_form-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.translation_fixed_form-a1.constant_dehomogenization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, A, and α satisfying the hypotheses. Write X=X₀ and Y=X₁. Because A belongs to BinaryForm ℂ n, every exponent vector e with a nonzero coefficient in A satisfies e(0)+e(1)=n; coefficients at all other exponent vectors vanish.
2. For each integer k with 0≤k≤n, define e_k by e_k(0)=n−k and e_k(1)=k, and let a_k be the coefficient of A at e_k. Every exponent vector of total degree n equals exactly one e_k: take k=e(1), obtain k≤n and e(0)=n−k, and use that Fin 2 consists of 0 and 1. Distinct k give distinct vectors because their values at 1 differ. The finite monomial expansion of A therefore gives A(X,Y)=Σ_{k=0}^n a_k X^(n−k)Y^k. This equality includes zero coefficients and follows coefficientwise also at exponent vectors outside total degree n.
3. Let D be the evaluation homomorphism into ℂ[t] sending complex scalars to constant polynomials, X to 1, and Y to t. Applying D to the expansion gives D(A)=Σ_{k=0}^n a_k t^k, since D preserves sums and products and 1^(n−k)=1. Thus the coefficient of t^k in D(A) is exactly a_k for each 0≤k≤n: among the displayed monomials only the k-th has that exponent.
4. By hypothesis D(A)=C(α). Comparing coefficients at zero gives a_0=α. Comparing coefficients at each k with 1≤k≤n gives a_k=0, because a constant polynomial has zero coefficient at every positive degree.
5. Substituting these coefficients into the expansion leaves only a_0 X^nY^0=αX^n. Hence A.val=MvPolynomial.C α * MvPolynomial.X (0:Fin 2)^n. When n=0 the expansion has only its k=0 term, so the same calculation proves the conclusion without a positive-degree assumption.

## Key steps

1. Use homogeneity to restrict nonzero coefficients to exponent vectors of total degree n.
2. Index those exponent vectors uniquely by the exponent of Y.
3. Dehomogenize the resulting expansion to a univariate polynomial with the same indexed coefficients.
4. Compare with the constant polynomial to eliminate every positive Y exponent.
5. Reconstruct αX^n, including the case n=0.

## Reference use

### local-project

Queries:
- `BinaryForm|binaryFormRepSL|def.*T\b|unipotent|translation|homogeneous`
- `IsHomogeneous|mem_homogeneousSubmodule|coeff.*eq_zero`
- `eval₂_monomial|eval₂_eq|eval₂_X|eval₂_C`
- `theorem coe_T_zpow|theorem coe_T_pow|def T :`
- `Polynomial.*[pP]eriodic|[pP]eriodic.*Polynomial|comp_X_add_C_eq_self|eq_C_of_periodic|eq_C_of_comp|dehomogen`
- `p02_es_177ebb5a_tff_(periodic_polynomial_constant|constant_dehomogenization)`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`
- `cmp Definitions/Def_HeckeEis_BinaryFormRep.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_tff_decomposition_types.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_tff_decomposition_instances.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/Polynomial/Taylor.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/tmp/p02_tff_decomposition_types.lean`
- `/tmp/p02_tff_decomposition_instances.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Active binary-form definitions match the snapshot byte-for-byte, and local mathlib is clean at the pinned revision. BinaryForm is the homogeneous submodule, and binarySubst uses column substitution, confirming that T^N substitutes Y by NX+Y. Polynomial.taylor_coeff supplies translation-coefficient infrastructure; IsHomogeneous.coeff_eq_zero and eval₂_monomial support homogeneous reconstruction. The snapshot-wide periodicity/dehomogenization search returned no matches. Both proposed names have no matches in the current DAG, node records, or Submission.lean. Both exact child types elaborate after import Submission. Explicit elaboration confirms Polynomial.instAdd, Polynomial.commSemiring, and the AddMonoidAlgebra multiplication and power instances underlying MvPolynomial. Transitive axiom checks for binaryFormRepSL_apply_coe, coe_T_zpow, taylor_coeff, IsHomogeneous.coeff_eq_zero, and eval₂_monomial report only propext, Classical.choice, and Quot.sound. These are interface and reference checks, not comparator acceptance of new proofs.
