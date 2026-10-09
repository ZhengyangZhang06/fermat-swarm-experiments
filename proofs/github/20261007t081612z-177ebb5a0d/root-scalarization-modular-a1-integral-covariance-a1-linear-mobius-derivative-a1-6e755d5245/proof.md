# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1.integral_covariance-a1`
- Child DAG node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n,A,F,P,σ,τ and the assumed coefficient derivatives. Write V=BinaryForm ℂ n and w₀=((σ·τ):ℂ). For each r=0,…,n, let d_r be the exponent index with d_r(0)=r and d_r(1)=n−r, and let b_r be the monomial with exponent d_r and coefficient one. Its total degree is n, so b_r belongs to V.
2. Every Q∈V has the expansion Q=Σ_{r=0}^n coeff d_r(Q) • b_r. Indeed, compare coefficients at an arbitrary exponent index d. If d(0)+d(1)≠n, homogeneity makes the coefficient of Q zero, and each b_r also has zero coefficient there. Otherwise r=d(0) satisfies r≤n and d(1)=n−r, hence d=d_r. This r is unique, so the coefficient of the displayed sum is exactly coeff d(Q). Polynomial coefficient extensionality and subtype extensionality prove the expansion.
3. Fix an output exponent index e and put λ_r=coeff e(A(b_r)). Applying A and then coefficient e to the expansion gives coeff e(A(Q))=Σ_{r=0}^n λ_r·coeff d_r(Q), using complex linearity and commutativity of complex multiplication. Consequently H_e(z)=coeff e(A(F(ofComplex z))) is this fixed finite linear combination of the input coefficient functions. The hypotheses and the constant-multiple and finite-sum derivative rules give H_e derivative Σ_{r=0}^n λ_r·coeff d_r(P) at w₀. Applying the same expansion to P identifies this derivative with coeff e(A(P)). All differentiation here is of complex-valued functions.
4. Write σ=(a b;c d), regarding its integer entries as complex numbers in formulas, and put j=cτ+d=jFactor(σ,τ). The determinant equation is ad−bc=1. For any u with Im u>0, cu+d≠0: if c≠0 its imaginary part c·Im u is nonzero, while if c=0 the determinant equation gives ad=1 and d≠0. The action in complex coordinates is T(u)=(au+b)/(cu+d); multiplying by the conjugate denominator gives Im T(u)=Im u/|cu+d|²>0. The quotient rule gives T′(τ)=[a(cτ+d)−c(aτ+b)]/j²=1/j². Define W(z)=((σ·ofComplex z):ℂ). On a neighborhood of τ contained in the open upper half-plane, ofComplex is the usual identification, so W agrees with T. Thus W has derivative 1/j² at τ and W(τ)=w₀. These locality and derivative facts are also recorded by UpperHalfPlane.eventuallyEq_coe_comp_ofComplex and the determinant-one specialization of UpperHalfPlane.hasStrictDerivAt_smul.
5. For every complex z, the point σ·ofComplex z already belongs to ℍ. Therefore UpperHalfPlane.ofComplex_apply gives ofComplex(W(z))=σ·ofComplex z. It follows that H_e(W(z))=coeff e(A(F(σ·ofComplex z))) for every z.
6. Apply the complex chain rule to the derivatives from steps 3 and 4, using W(τ)=w₀. The function in step 5 has derivative coeff e(A(P))·(1/j²)=coeff e(A(P))/j² at τ. Since e was arbitrary, this proves the asserted statement for every coefficient, including indices outside degree n.

## Key steps

1. Construct the degree-n monomials and prove their finite expansion by coefficient extensionality.
2. Express each output coefficient of A as a fixed finite linear combination of input coefficients.
3. Differentiate that finite sum at the complex coordinate of στ.
4. Compute the Möbius derivative at τ as 1/jFactor(σ,τ)² and transfer it to the ofComplex extension.
5. Identify the desired function exactly as the scalar composition using ofComplex_apply.
6. Apply the complex chain rule and rewrite multiplication by the reciprocal square as division.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|binaryFormRepSL_linePow|eichlerShimuraMap_injective|hasStrictDerivAt_smul|SL_slash_apply`
- `ofComplex|eventually|hasStrictDerivAt_smul`
- `coeff.*HasDerivAt|HasDerivAt.*coeff|linear.*deriv|pullback.*deriv|inverse.*linePow|linePow.*inv`
- `p02_es_177ebb5a_ic_(linear_mobius_derivative|inverse_linepow)`
- `HasDerivAt\.(sum|fun_sum)|theorem.*(sum|fun_sum)`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_ic_interfaces_177ebb5a.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/tmp/p02_ic_interfaces_177ebb5a.lean`

The snapshot pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Its definitions supply coefficientwise IsEichlerIntegral, the binary-form representation, jFactor_ne_zero, and binaryFormRepSL_linePow. Mathlib supplies the local ofComplex identities, Möbius derivative, finite-sum differentiation, and SL_slash_apply. The project helper search found only the defining coefficient derivative occurrence, with no matching transport or inverse-line helper. The DAG reserves a different general linear-derivative theorem in another branch; neither proposed name occurred in the searched declarations or run metadata. Both exact proposed types elaborated as Prop after import Submission. Lean inferred UpperHalfPlane.SLAction.toSMul and the binary-form submodule's complex module instance; an explicit equality also verified agreement with the mapGL action. Compared source files matched the snapshot, and all nine installed dependencies matched their pins with clean tracked sources. Transitive axiom queries for the cited infrastructure returned only propext, Classical.choice, and Quot.sound. These are interface and infrastructure checks, not comparator acceptance of child implementations.
