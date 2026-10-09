# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_exists-a1`
- Child DAG node: `root.primitive_exists-a1.scalar_primitive-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a with the stated differentiability hypothesis. Put H={z∈ℂ : Im z>0} and D={w∈ℂ : |w|<1}. Both sets are open, so differentiability within either set at one of its points gives ordinary complex differentiability there. Define φ(w)=i(1+w)/(1−w) and ψ(z)=(z−i)/(z+i), using the total complex division operation to define these functions on all of ℂ.
2. For w∈D, 1−w is nonzero, and direct expansion gives Im φ(w)=(1−|w|²)/|1−w|²>0. For z∈H, z+i is nonzero since its imaginary part is Im z+1>0. Expanding squared norms gives |z+i|²−|z−i|²=4 Im z>0, hence |ψ(z)|<1. Thus φ maps D into H and ψ maps H into D.
3. For z∈H, the identities 1+ψ(z)=2z/(z+i) and 1−ψ(z)=2i/(z+i) imply φ(ψ(z))=z. For w∈D, the identities φ(w)−i=2iw/(1−w) and φ(w)+i=2i/(1−w) imply ψ(φ(w))=w. The quotient rule, with the nonzero denominators established above, gives φ′(w)=2i/(1−w)² on D and ψ′(z)=2i/(z+i)² on H. In particular φ′(ψ(z))ψ′(z)=1, by substituting 1−ψ(z)=2i/(z+i).
4. Define b(w)=a(φ(w))·2i/(1−w)². Since φ maps D into H, the composition a∘φ is holomorphic on D. The other factor is a rational function whose denominator does not vanish on D, so b is holomorphic on D. Apply DifferentiableOn.isExactOn_ball from the pinned Mathlib/Analysis/Complex/HasPrimitives.lean with center 0 and radius 1. Unfolding Complex.IsExactOn yields B : ℂ → ℂ with HasDerivAt B (b w) w for every w∈D.
5. Set A(z)=B(ψ(z)). For z∈H, ψ(z)∈D, so the complex chain rule gives A′(z)=b(ψ(z))ψ′(z)=a(φ(ψ(z)))φ′(ψ(z))ψ′(z)=a(z). Each derivative used here is an ordinary derivative at the indicated point, so this establishes HasDerivAt A (a z) z, exactly as required.

## Key steps

1. Verify the Cayley maps send the disk and upper half-plane into one another.
2. Compute their inverse identities and derivatives, including the derivative product equal to one.
3. Apply the pinned disk-primitive theorem to the pulled-back differential.
4. Compose its primitive with the inverse Cayley map and apply the chain rule.

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
