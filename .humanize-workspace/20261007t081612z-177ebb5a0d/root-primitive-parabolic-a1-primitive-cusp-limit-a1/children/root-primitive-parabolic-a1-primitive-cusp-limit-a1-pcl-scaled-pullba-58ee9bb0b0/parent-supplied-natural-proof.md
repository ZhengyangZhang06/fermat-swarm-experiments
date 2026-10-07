# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1`
- Child DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scaled_pullback_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, f, F, the Eichler-integral hypothesis, σ, d, and τ. Write the entries of σ as α, β, γ, δ, so αδ−βγ=1, and put j=γτ+δ. The denominator j is nonzero on the upper half-plane. Define m(z)=(αz+β)/(γz+δ), L(z)=(zX+Y)^n, and R=binaryFormRepSL ℂ n σ.
2. On the open upper half-plane, m(z) is the complex coordinate of σ·ofComplex z. Its image also lies in the upper half-plane. Thus, in a neighborhood of τ, ofComplex(m(z))=σ·ofComplex z. In particular, for φ(w)=coeff_d(F(ofComplex w)), the function in the conclusion agrees locally with φ∘m. The Eichler-integral hypothesis at σ·τ gives φ'(m(τ))=f(σ·τ)coeff_d(L(m(τ))).
3. The quotient rule applies at τ because j≠0. It gives m'(τ)=(α(γτ+δ)−γ(ατ+β))/j²=(αδ−βγ)/j²=j^(−2). The complex chain rule therefore gives the derivative of the required coefficient function as f(σ·τ)coeff_d(L(m(τ)))j^(−2).
4. The identity binaryFormRepSL_linePow gives R(L(τ))=j^n L(m(τ)). Taking the d-coefficient, using its complex linearity, gives coeff_d(R(L(τ)))=j^n coeff_d(L(m(τ))).
5. Since j≠0, multiplication of integer powers gives j^{−(n+2)}j^n=j^(−2). Consequently j^{−(n+2)}f(σ·τ)coeff_d(R(L(τ))) equals the derivative obtained in step 3. Local equality preserves HasDerivAt, so this proves exactly the asserted derivative for the total function using ofComplex.

## Key steps

1. Identify the pullback locally with composition by the Möbius rational function.
2. Differentiate the Möbius function using determinant one and its nonzero denominator.
3. Apply the coefficientwise Eichler-integral hypothesis and chain rule.
4. Take coefficients in binaryFormRepSL_linePow.
5. Combine the integer powers of the nonzero automorphy factor.

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
