# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1`
- Child DAG node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.binary_form_jet_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, P, r and z. Put X=X₀, Y=X₁, D=∂/∂Y and dₖ=single 0 (n−k)+single 1 k for 0≤k≤n. Write A(k,s) for the complex cast of Nat.descFactorial k s. Thus A(k,0)=1 and A(k,s+1)=A(k,s)·(k−s), with natural-number subtraction before casting.
2. Homogeneity of P says that a nonzero coefficient at d has d(0)+d(1)=n. Taking k=d(1) gives k≤n and d(0)=n−k, so d=dₖ. The vectors dₖ are pairwise distinct because their coordinate 1 is k. Comparing every coefficient therefore gives P=Σₖ C(coeff dₖ P)X^(n−k)Y^k, over k∈Fin(n+1): if the exponent has total degree n exactly one summand can contribute, and otherwise both sides have zero coefficient.
3. For any 0≤k≤n and any complex a, induction on s proves D^s(C(a)X^(n−k)Y^k)=C(a A(k,s))X^(n−k)Y^(k−s) for every natural s. At s=0 this follows from A(k,0)=1. For the induction step, D annihilates constant coefficients and X. If s<k, differentiating the Y power multiplies its coefficient by k−s and replaces its exponent by (k−s)−1=k−(s+1); the recurrence for A gives the claimed coefficient. If k≤s, the Y exponent is zero and the derivative is zero; the desired right side is also zero because A(k,s+1)=A(k,s)·0=0. This completes the induction, including orders exceeding k.
4. Since D is complex-linear, its r-fold iterate is complex-linear. Apply it termwise to the fixed finite expansion from step 2 and use step 3 with a=coeff dₖ P.
5. Evaluate the resulting equality at X=1 and Y=−z. Evaluation preserves finite sums and products, and each summand becomes coeff dₖ P · A(k,r) · (−z)^(k−r). This is the asserted identity, with all subtractions interpreted in the natural numbers and no restriction on r.

## Key steps

1. Use homogeneity to identify every supported exponent uniquely with d_k.
2. Expand P over the fixed index type Fin(n+1).
3. Induct on the derivative order to obtain the falling-factorial monomial formula, including vanishing beyond the Y-degree.
4. Apply linearity of iterated formal differentiation to the expansion.
5. Evaluate at X=1 and Y=−z.

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
