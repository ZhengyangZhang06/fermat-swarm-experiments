# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1`
- Child DAG node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1.linear_map_coefficient_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, A, and e. For each r∈Fin(n+1), define d_r=single 0 r.val+single 1 (n−r.val). Since r.val≤n, its degree is r.val+(n−r.val)=n. The monomial m_r=monomial d_r 1 is therefore homogeneous of degree n, by monomial homogeneity. Thus b_r=⟨m_r, its membership proof⟩ is an element of V=BinaryForm ℂ n.
2. Define c(r)=coeff e((A b_r).val). This defines a function Fin(n+1)→ℂ before choosing Q, so it is independent of Q.
3. Fix any Q∈V and write a_r=coeff d_r(Q.val). Apply binary_form_monomial_expansion to obtain Q.val=Σ_r a_r • m_r. The inclusion of the submodule V into the polynomial space preserves finite sums and scalar multiplication, so the right side is the underlying polynomial of Σ_r a_r • b_r. Injectivity of this inclusion, or subtype extensionality, gives Q=Σ_r a_r • b_r in V.
4. Apply A to this equality. Additivity and complex linearity give A Q=Σ_r a_r • A b_r. Taking underlying polynomials and then coefficient e, and using coefficient additivity and compatibility with scalar multiplication, gives coeff e((A Q).val)=Σ_r a_r·coeff e((A b_r).val).
5. Substitute the definitions of a_r and c(r), and commute the two complex factors in each summand. The result is coeff e((A Q).val)=Σ_r c(r)·coeff d_r(Q.val). Since Q was arbitrary, the function c from step 2 satisfies the required universal identity, proving the existential conclusion.

## Key steps

1. Construct the degree-n monomials as elements of the homogeneous submodule.
2. Define the fixed output coefficients c(r) by applying A to those monomials.
3. Lift the sibling's polynomial expansion to an equality inside BinaryForm.
4. Apply the linear map and then the coefficient functional.
5. Commute complex scalar factors and conclude the uniform identity for every Q.

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
