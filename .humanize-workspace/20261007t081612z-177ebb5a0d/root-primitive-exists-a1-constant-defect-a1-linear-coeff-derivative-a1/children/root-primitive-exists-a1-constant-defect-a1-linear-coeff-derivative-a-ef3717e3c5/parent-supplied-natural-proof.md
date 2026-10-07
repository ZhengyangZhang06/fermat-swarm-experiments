# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1`
- Child DAG node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1.binary_form_monomial_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n and Q as stated. Write d_r=single 0 r.val+single 1 (n−r.val) and m_r=monomial d_r 1. Since r.val<n+1, we have r.val≤n. Evaluating the two single functions gives d_r(0)=r.val and d_r(1)=n−r.val. Hence degree(d_r)=r.val+(n−r.val)=n.
2. Let S=Σ_{r∈Fin(n+1)} coeff d_r(Q.val) • m_r. Fix an arbitrary exponent d:Fin 2→₀ℕ. Coefficients commute with finite sums and scalar multiplication, and coeff d(m_r) equals 1 when d_r=d and 0 otherwise. Thus coeff d(S)=Σ_r coeff d_r(Q.val)·(if d_r=d then 1 else 0).
3. Suppose degree(d)≠n. Because Q.val is homogeneous of degree n, coeff d(Q.val)=0. Every d_r has degree n by step 1, so d_r≠d for every r. Every summand in step 2 is therefore zero, giving coeff d(S)=0=coeff d(Q.val).
4. Suppose instead degree(d)=n. Since Fin 2 consists of 0 and 1, this says d(0)+d(1)=n. Consequently d(0)≤n and n−d(0)=d(1). Let r₀∈Fin(n+1) have value d(0), which is permitted by d(0)<n+1. The equalities at coordinates 0 and 1 show d_{r₀}=d by extensionality of finitely supported functions.
5. If d_r=d, evaluation at coordinate 0 gives r.val=d(0)=r₀.val, hence r=r₀ by extensionality of Fin. The sum in step 2 therefore has exactly one potentially nonzero term, at r₀, and equals coeff d_{r₀}(Q.val)=coeff d(Q.val).
6. Steps 3 and 5 establish equality of the coefficients of Q.val and S at every exponent d. Polynomial coefficient extensionality gives Q.val=S, which is the asserted expansion.

## Key steps

1. Define the degree-n exponent d_r and compute its two coordinates and total degree.
2. Compute each coefficient of the proposed finite sum using the monomial coefficient formula.
3. Use homogeneity to handle exponent indices of degree different from n.
4. Represent every degree-n exponent uniquely as d_r.
5. Evaluate the resulting single nonzero summand and apply polynomial coefficient extensionality.

## Reference use

### local-project

Queries:
- `binaryForm.*(basis|[Ee]xpan|[Cc]oeff)|BinaryForm.*(basis|[Ee]xpan)|coeff.*HasDerivAt|HasDerivAt.*coeff`
- `basis|coeff_eq_zero|isHomogeneous_monomial|homogeneousSubmodule|sum_monomial|def IsHomogeneous`
- `theorem (coeff_monomial|coeff_smul|coeff_sum|ext)|lemma (coeff_monomial|coeff_smul|coeff_sum)|finsetSum_coeff|degree_eq_sum|degree_single|degree_add|degree_eq_weight_one`
- `theorem HasDerivAt.(sum|const_mul)|lemma HasDerivAt.(sum|const_mul)`
- `p02_es_177ebb5a_lcd_monomial_expansion|p02_es_177ebb5a_lcd_coeff_linear_combination`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_lcd_decomposition_types.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Finsupp/Weight.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/tmp/p02_lcd_decomposition_types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous polynomial submodule. The project search found the defining coefficientwise IsEichlerIntegral condition but no matching binary-form expansion or derivative helper. Mathlib supplies monomial homogeneity, off-degree coefficient vanishing, coefficient extensionality and linearity, exponent degree identities, HasDerivAt.fun_sum, and HasDerivAt.const_mul. Neither proposed identifier occurred in the searched project or run metadata. Both exact proposed types elaborated after import Submission under Lean 4.33.1. Instance synthesis confirmed the polynomial scalar action is AddMonoidAlgebra.algebra.toSMul. All installed dependencies matched their pinned revisions with clean tracked sources; the six transitive project definition files and five inspected mathlib files matched the snapshot byte-for-byte. Transitive axiom checks of the cited infrastructure returned only propext, Classical.choice, and Quot.sound. These checks validate the interfaces and infrastructure, not comparator acceptance of the proposed children.
