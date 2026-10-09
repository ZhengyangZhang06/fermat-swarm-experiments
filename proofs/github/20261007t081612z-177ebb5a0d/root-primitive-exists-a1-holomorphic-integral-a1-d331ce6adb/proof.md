# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_exists-a1`
- Child DAG node: `root.primitive_exists-a1.holomorphic_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n and h satisfying the hypothesis, and write H={z∈ℂ : Im z>0} and h̃(z)=h(ofComplex z). For each integer r with 0≤r≤n, define a_r(z)=(binom(n,r):ℂ)h̃(z)z^r. Constants and powers are holomorphic, so the hypothesis and the product rule make each a_r complex differentiable on H.
2. Apply scalar_primitive to each of these finitely many functions. Choose A_r : ℂ → ℂ such that HasDerivAt A_r (a_r(z)) z holds for every z∈H and every 0≤r≤n.
3. Write X=X₀ and Y=X₁ in MvPolynomial (Fin 2) ℂ. For τ∈ℍ, define the underlying polynomial of F(τ) to be Σ_{r=0}^n C(A_r(τ))X^rY^(n−r), where τ is coerced to ℂ. Each summand is homogeneous of degree r+(n−r)=n, since r≤n. Their sum therefore belongs to BinaryForm ℂ n, defining F with the required codomain.
4. For 0≤r≤n, let e_r be the exponent index with e_r(0)=r and e_r(1)=n−r. These indices are distinct. Since Fin 2 has precisely the two elements 0 and 1, any exponent index d has total degree d(0)+d(1). If this degree equals n, then r=d(0) satisfies r≤n and d=e_r. Consequently coeff e_r (F(τ))=A_r(τ), while every coefficient whose index has degree different from n is zero. The binomial expansion gives (τX+Y)^n=Σ_{r=0}^n C((binom(n,r):ℂ)τ^r)X^rY^(n−r), so its e_r coefficient is (binom(n,r):ℂ)τ^r and its coefficients outside degree n are zero.
5. Fix τ∈ℍ. The set H is an open neighborhood of its complex coordinate. On this neighborhood the complex coordinate of ofComplex z equals z. Hence, for d=e_r, the function z↦coeff d (F(ofComplex z)) agrees near τ with A_r(z). Its derivative at τ is therefore a_r(τ)=(binom(n,r):ℂ)h(τ)τ^r, using ofComplex τ=τ. By commutativity this equals h(τ)·coeff d ((τX+Y)^n).
6. If d has degree different from n, the function z↦coeff d (F(ofComplex z)) is identically zero because every value of F is homogeneous of degree n. Its derivative is zero, and the required derivative value is also zero by the binomial coefficient computation. These two cases cover every d, establishing exactly IsEichlerIntegral n h F.

## Key steps

1. Form the finitely many holomorphic coefficient functions binom(n,r)h(z)z^r.
2. Apply scalar_primitive to obtain their primitives.
3. Assemble the primitives into a homogeneous polynomial of degree n.
4. Identify every degree-n coefficient and every vanishing off-degree coefficient.
5. Use local agreement of ofComplex with the identity to verify the frozen derivative predicate.

## Reference use

### local-project

Queries:
- `rg -n 'IsEichlerIntegral|IsEquivariantPrimitiveWith|binaryFormRepSL_linePow|eichlerShimuraMap_injective|isExactOn_ball' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b`
- `grep -R -n -E 'IsEichlerIntegral|IsEquivariantPrimitiveWith|binaryFormRepSL_linePow|eichlerShimuraMap_injective|isExactOn_ball' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b --include='*.lean'`
- `upperHalfPlane.*(primitive|Primitive)|primitive.*upperHalfPlane|isExactOn_upperHalfPlane|p02_es_177ebb5a_primitive_exists_(scalar_primitive|holomorphic_integral|constant_defect)`
- `coeff_eq_zero|mem_homogeneousSubmodule|IsHomogeneous`
- `eqOn_of_deriv|eq_of_hasDerivAt|is_const|eq_of_deriv`
- `slash_action_eqn|slash_action_eq`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_primitive_exists_interfaces.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/tmp/p02_primitive_exists_interfaces.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. rg was unavailable, so searches used grep. The definitions confirm the coefficientwise IsEichlerIntegral predicate, constant-defect conclusion, and binaryFormRepSL_linePow identity. HasPrimitives supplies DifferentiableOn.isExactOn_ball; Manifold supplies the ofComplex holomorphy equivalence and Möbius derivative; SlashInvariantForms supplies the determinant-one transformation law; Homogeneous supplies coefficient vanishing outside the prescribed degree; MeanValue supplies zero-derivative constancy. The searched project Definitions/P2M and mathlib Analysis sources contained no upper-half-plane primitive theorem matching the stated search patterns. The proposed identifiers had no matches in the current declarations or node metadata. All three exact proposed types elaborated with only import Submission under Lean 4.33.1; explicit elaboration confirmed the prescribed mapGL image of Gamma0 and matrix algebra instances. All installed dependencies matched their recorded revisions with clean tracked sources; the six transitive project definition files and consulted mathlib files matched the snapshot. Axiom checks of the cited primitive, representation, transformation, derivative, constancy, and predicate declarations returned only propext, Classical.choice, and Quot.sound. These are interface and infrastructure checks, not comparator acceptance of new proofs.
