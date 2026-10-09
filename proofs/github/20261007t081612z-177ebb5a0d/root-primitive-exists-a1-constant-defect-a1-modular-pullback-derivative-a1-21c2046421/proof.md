# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_exists-a1.constant_defect-a1`
- Child DAG node: `root.primitive_exists-a1.constant_defect-a1.modular_pullback_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data, γ,e,τ. Let g be the determinant-one integer matrix underlying γ, with entries a,b,c,d, and regard these entries as complex numbers when used in formulas. Put j(w)=cw+d. For w in the upper half-plane, j(w)≠0: if c≠0, its imaginary part c·Im(w) is nonzero; if c=0, the determinant equation ad−bc=1 gives ad=1 and hence d≠0. In particular j(τ)=HeckeEis.jFactor g τ is nonzero.
2. Set T(w)=(aw+b)/(cw+d). Multiplying numerator and denominator by the conjugate of cw+d shows Im(T(w))=(ad−bc)Im(w)/|cw+d|²=Im(w)/|cw+d|². Thus T sends the upper half-plane into itself and is the complex coordinate of the action of g. The quotient derivative at τ is [a(cτ+d)−c(aτ+b)]/(cτ+d)²=(ad−bc)/j(τ)²=1/j(τ)². Since the upper half-plane is open, ofComplex agrees with the usual coordinate inclusion throughout a neighborhood of τ. Consequently G(w)=((g·ofComplex w):ℂ) has derivative 1/j(τ)² at τ, and G(τ)=((g·τ):ℂ). This is also the determinant-one specialization of UpperHalfPlane.hasStrictDerivAt_smul.
3. Define H_e(w)=coeff e(F(ofComplex w)). The IsEichlerIntegral hypothesis at g·τ gives HasDerivAt H_e [f(g·τ)·coeff e(L(g·τ))] ((g·τ):ℂ). For every w, ofComplex(G(w))=g·ofComplex w because the latter is already an upper-half-plane point. Hence H_e∘G is exactly w↦coeff e(F(g·ofComplex w)). The complex chain rule and step 2 give its derivative at τ as f(g·τ)·coeff e(L(g·τ))/j(τ)².
4. Since γ belongs to Γ, slash invariance of f gives f(g·τ)=j(τ)^((n:ℤ)+2)f(τ). This is SlashInvariantForm.slash_action_eqn_SL'' for the prescribed real matrix image, with the denominator identified with jFactor. The integer exponent is the cast of the natural number n+2, so its power equals the natural power j(τ)^(n+2). Since j(τ)≠0 and j(τ)^(n+2)=j(τ)^n·j(τ)², the derivative from step 3 simplifies to f(τ)·j(τ)^n·coeff e(L(g·τ)).
5. The pinned identity HeckeEis.binaryFormRepSL_linePow gives ρ(γ)L(τ)=j(τ)^n • L(g·τ). Taking coefficient e yields coeff e(ρ(γ)L(τ))=j(τ)^n·coeff e(L(g·τ)). Substitute this into step 4 and associate the complex products. The derivative is precisely f(τ)·coeff e(ρ(γ)L(τ)), proving the required HasDerivAt statement for the arbitrary γ,e,τ.

## Key steps

1. Prove the automorphy factor is nonzero on the upper half-plane.
2. Compute the modular action's complex derivative as the inverse square of that factor.
3. Apply the coefficientwise Eichler derivative and the complex chain rule.
4. Use slash invariance and cancel the square from the weight n+2 factor.
5. Use binaryFormRepSL_linePow to identify the resulting coefficient with that of ρ(γ)L(τ).

## Reference use

### local-project

Queries:
- `rg -n 'IsEichlerIntegral|binaryFormRepSL_linePow|hasStrictDerivAt_smul' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b`
- `grep -R -n -E 'IsEichlerIntegral|IsEquivariantPrimitiveWith|binaryFormRepSL_linePow' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project --include='*.lean'`
- `hasDerivAt|ofComplex|convex`
- `slash_action_eqn_SL|slash_action_eqn`
- `coeff_eq_zero|mem_homogeneousSubmodule|IsHomogeneous|sum_monomial`
- `eq_of_hasDerivAt|eqOn_of_deriv|is_const|eq_of_deriv`
- `coeff.*HasDerivAt|HasDerivAt.*coeff|binaryForm.*[Dd]eriv|[Dd]eriv.*binaryForm`
- `p02_es_177ebb5a_cd_linear_coeff_derivative`
- `p02_es_177ebb5a_cd_modular_pullback_derivative`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_constant_defect_interfaces.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/tmp/p02_constant_defect_interfaces.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. rg was unavailable; searches continued with grep and Python. The definitions provide coefficientwise IsEichlerIntegral, jFactor_ne_zero, and binaryFormRepSL_linePow. Mathlib supplies homogeneous coefficient vanishing, the Möbius derivative, the determinant-one slash transformation law, and zero-derivative constancy. The project derivative-helper search found only the defining IsEichlerIntegral occurrence, with no matching helper. Neither proposed identifier occurred in the searched project declarations or run metadata. Both exact proposed types elaborated after import Submission under Lean 4.33.1. Explicit elaboration confirmed the mapGL image in the cusp-form type, matrix algebra instances, and UpperHalfPlane.SLAction. All installed dependencies matched their pinned revisions with clean tracked sources; the six transitive project definition files and inspected mathlib files matched the snapshot. Transitive axiom checks of the cited infrastructure returned only propext, Classical.choice, and Quot.sound. These checks validate interfaces and reusable infrastructure, not acceptance of new child proofs.
