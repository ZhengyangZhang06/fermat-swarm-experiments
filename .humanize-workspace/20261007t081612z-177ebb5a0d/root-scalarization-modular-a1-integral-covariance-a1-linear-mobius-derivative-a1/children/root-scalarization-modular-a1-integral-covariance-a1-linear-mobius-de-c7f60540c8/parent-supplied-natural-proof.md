# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1`
- Child DAG node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.scalar_mobius_pullback-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix h, v, σ, τ and the derivative hypothesis. Write the integer entries of σ as a,b,c,d, and use their complex casts in complex expressions. Its determinant equation gives ad−bc=1. Set t=(τ : ℂ), w₀=((σ • τ : ℍ) : ℂ), and j=ct+d=HeckeEis.jFactor σ τ.
2. For any complex u with positive imaginary part, cu+d is nonzero. If c=0, the determinant equation gives ad=1, hence d≠0. If c≠0, the imaginary part of cu+d is the nonzero real number c·Im(u), since c and d are real and Im(u)>0. In particular j≠0. The complex-coordinate formula for the action is T(u)=(au+b)/(cu+d). To verify its upper-half-plane value directly, expand (au+b)·conj(cu+d): its imaginary part is (ad−bc)·Im(u)=Im(u). Dividing by |cu+d|² therefore gives Im(T(u))=Im(u)/|cu+d|²>0.
3. The affine numerator and denominator of T have derivatives a and c at t. Since j≠0, the complex quotient rule gives T′(t)=[a(ct+d)−(at+b)c]/j²=(ad−bc)/j²=1/j².
4. Define W(z)=((σ • UpperHalfPlane.ofComplex z : ℍ) : ℂ). The open set U={z : ℂ | 0<Im(z)} contains t. For z∈U, the complex coordinate of ofComplex z is z, and the action formula therefore gives W(z)=T(z). Equality on this neighborhood transfers the derivative in step 3 to W at t. Also ofComplex t=τ, so W(t)=w₀. These locality and action-derivative facts agree with UpperHalfPlane.eventuallyEq_coe_comp_ofComplex and UpperHalfPlane.hasStrictDerivAt_smul, specialized to the real general-linear image of σ, whose determinant is 1 and whose denominator is j by HeckeEis.jFactor_eq_denom.
5. Put H(z)=h(UpperHalfPlane.ofComplex z). The hypothesis gives H derivative v at w₀=W(t). The scalar complex chain rule applied to H and W therefore gives H∘W derivative v·(1/j²) at t.
6. For every complex z, the point σ • ofComplex z belongs to ℍ. Consequently UpperHalfPlane.ofComplex_apply gives ofComplex(W(z))=σ • ofComplex z. Thus H(W(z))=h(σ • ofComplex z) for every z. Substitute this function equality into step 5 and simplify v·(1/j²)=v/j². This is exactly the required derivative statement.

## Key steps

1. Use determinant one and positive imaginary part to show the Möbius denominator is nonzero.
2. Compute the quotient derivative as 1/jFactor(σ,τ)².
3. Transfer the derivative to the actual action-coordinate function using local equality on the upper half-plane.
4. Apply the scalar chain rule at the coordinate of σ • τ.
5. Use ofComplex_apply to identify the composite globally and simplify its derivative.

## Reference use

### local-project

Queries:
- `BinaryForm|eventuallyEq_coe_comp_ofComplex|hasStrictDerivAt_smul`
- `basis|monomial|finite|coeff`
- `linear_coeff_derivative|linear_mobius_derivative|scalar_pullback`
- `theorem HasDerivAt.(sum|fun_sum|const_mul|comp)|lemma HasDerivAt.(sum|fun_sum|const_mul|comp)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous polynomial submodule. The inspected sources supply homogeneous monomials, vanishing coefficients outside the specified degree, jFactor_eq_denom, jFactor_ne_zero, hasStrictDerivAt_smul, ofComplex_apply, and scalar sum, multiplication, and chain rules. The project search for linear_coeff_derivative|linear_mobius_derivative|scalar_pullback returned no matches. The two inspected project definitions and three inspected homogeneous/upper-half-plane mathlib files match the installed sources byte-for-byte; installed mathlib has the pinned revision and clean Git status. Axiom queries for the six cited homogeneous, jFactor, and upper-half-plane lemmas returned only propext, Classical.choice, and Quot.sound.
