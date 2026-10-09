# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1.integral_covariance-a1`
- Child DAG node: `root.scalarization_modular-a1.integral_covariance-a1.inverse_linepow_transport-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n,σ,τ. Put ρ=binaryFormRepSL ℂ n, L₀=linePow n (τ:ℂ), L₁=linePow n ((σ·τ):ℂ), and j=jFactor(σ,τ). By HeckeEis.jFactor_ne_zero, j≠0. Hence q=j^n is nonzero, including when n=0, and q⁻¹q=1 in ℂ.
2. The pinned theorem HeckeEis.binaryFormRepSL_linePow states ρ(σ)(L₀)=q • L₁. Apply the complex-linear map ρ(σ⁻¹) to both sides. Its compatibility with scalar multiplication gives ρ(σ⁻¹)(ρ(σ)(L₀))=q • ρ(σ⁻¹)(L₁).
3. Since ρ is a representation, ρ(σ⁻¹) composed with ρ(σ) equals ρ(σ⁻¹σ)=ρ(1), which is the identity endomorphism. Thus step 2 becomes L₀=q • ρ(σ⁻¹)(L₁).
4. Multiply this equality by the scalar q⁻¹. Associativity of scalar multiplication and q⁻¹q=1 give q⁻¹ • L₀=ρ(σ⁻¹)(L₁). Reverse the equality and substitute q=j^n and the definitions of L₀,L₁. This is exactly the required identity.

## Key steps

1. Use the nonzero automorphy factor to obtain an invertible scalar jFactor(σ,τ)^n.
2. Apply ρ(σ⁻¹) to binaryFormRepSL_linePow and move the scalar through the linear map.
3. Cancel the representation factors using σ⁻¹σ=1.
4. Multiply by the reciprocal scalar and orient the resulting equality.

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
