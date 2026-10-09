# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1`
- Child DAG node: `root.scalarization_modular-a1.holomorphic_scalarization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let U={z∈ℂ:Im z>0}. For 0≤r≤n, let a_r(z) be the coefficient of X^rY^(n−r) in E(ofComplex z). Homogeneity of degree n gives the polynomial identity E(ofComplex z)=Σ_{r=0}^n a_r(z)X^rY^(n−r). Indeed, every nonzero coefficient has total degree n, and every two-variable monomial of that degree occurs exactly once in this sum.
2. Fix z∈U and regard it as τ=⟨z,Im z>0⟩∈ℍ. Apply IsEichlerIntegral to the coefficient index of X^rY^(n−r) and to τ. Its conclusion is a HasDerivAt statement for a_r at z. Thus a_r is complex differentiable at every point of U, and consequently DifferentiableOn ℂ a_r U. This uses only the derivative assertion, not differentiability of h.
3. Evaluation of the expansion at (1,−z) gives P(z)=Σ_{r=0}^n a_r(z)(−z)^(n−r). Every function z↦(−z)^(n−r) is a complex polynomial and hence differentiable everywhere. Products with the differentiable coefficient functions, followed by a finite sum, are differentiable on U.
4. The displayed finite sum equals the exact function in the statement, including its use of ofComplex. Therefore it proves the asserted DifferentiableOn proposition. The argument also covers n=0, when the sum has one term.

## Key steps

1. Expand each homogeneous binary form in the fixed degree-n monomial basis.
2. Apply IsEichlerIntegral to obtain differentiability of each coefficient on the upper half-plane.
3. Evaluate the expansion at (1,−z).
4. Use closure of differentiability under products, powers, and finite sums.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|binaryFormRepSL_linePow|eval_smul_of_isHomogeneous|binaryFormRepSL_apply_coe`
- `exp_decay_atImInfty|isBoundedAt_iff|isCusp_SL2Z_iff|isCusp_iff_isCusp_SL2Z|isArithmetic_iff_finiteIndex|instFiniteIndexGamma0|Gamma_normal|ModularGroup_T_pow_mem_Gamma`
- `scalarization|equivariant.*bounded|p02_es_177ebb5a_sm_`
- `hasStrictDerivAt_smul|Gamma_le_Gamma0|MDifferentiable.slash|isBoundedAtImInfty_iff`
- `def ofComplex|ofComplex_apply|ofComplex.*vadd|vadd.*ofComplex`
- `/runtime/bin/rg -n 'p02_es_177ebb5a_sm_' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project Submission.lean Definitions Theorems P2M Fermat .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_sm_typecheck.lean`
- `git -C .lake/packages/mathlib status --short`
- `git -C .lake/packages/mathlib rev-parse HEAD`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`

The snapshot pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Searches used /runtime/bin/rg after locating it outside PATH. The definitions confirm coefficientwise differentiation, the substitution convention, homogeneity, and the line-power transformation identity. Mathlib supplies the precise SL₂ slash action, exponential decay with periodicity/holomorphy/boundedness hypotheses, arithmetic cusp classification, and the full single-scaling-matrix criterion. No existing scalarization or equivariant-boundedness helper matched in the searched project directories; the proposed identifier prefix matched neither project declarations nor active DAG records. All five exact types elaborated after import Submission under Lean 4.33.1. Instance inspection returned ModularForm.SLAction, and the explicit real subgroup image uses Matrix.semiring. The installed dependency revisions match their pins with clean tracked sources; the transitive project definition files and inspected mathlib interfaces match the snapshot. Axiom queries for the reused representation, homogeneity, manifold, slash, decay, finite-index, and cusp results returned only propext, Classical.choice, and Quot.sound. These are interface and provenance checks, not comparator acceptance of new proofs.
