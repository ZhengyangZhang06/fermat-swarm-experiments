# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1`
- Child DAG node: `root.scalarization_modular-a1.all_cusps-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put Γ=Γ₀(N), ΓR=Γ.map(mapGL ℝ), ρ=binaryFormRepSL ℂ n, and p(z)=E(z)(1,−z). Since N≠0, reduction modulo N has finite target. Its kernel Γ(N) therefore has finite index and is contained in Γ₀(N), which also has finite index. These facts are recorded in Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean, including CongruenceSubgroup.instFiniteIndexGamma0. Subgroup.isArithmetic_iff_finiteIndex in ArithmeticSubgroups.lean makes ΓR arithmetic. Fix a cusp c of ΓR. By Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z and isCusp_SL2Z_iff' in Cusps.lean, choose σ∈SL₂(ℤ) such that mapGL ℝ σ sends infinity to c.
2. Put k=n+2, T_N=T^N, u=f|_kσ, and G(z)=ρ(σ⁻¹)E(σz). The entries of T_N are (1 N;0 1), so it belongs to Γ(N). This subgroup is the kernel of reduction and hence normal. Therefore γ=σT_Nσ⁻¹ belongs to Γ(N) and consequently to Γ. Since σT_N=γσ, the slash composition law and the slash invariance of f give (f|_kσ)|_kT_N=(f|_kγ)|_kσ=f|_kσ. The automorphy denominator of T_N is one, so u(z+N)=u(z).
3. The cusp form f is holomorphic, and the slash action preserves holomorphy by MDifferentiable.slash in Mathlib/NumberTheory/ModularForms/Basic.lean. Hence u is holomorphic and continuous. The cusp-form vanishing condition at c, applied to mapGL ℝ σ, gives UpperHalfPlane.IsZeroAtImInfty u. This also gives IsBoundedAtImInfty u. The function u∘ofComplex is periodic with real period N: on the upper half-plane this is step 2, while on its complement both arguments have nonpositive imaginary part and ofComplex has the same fixed value, by UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos in Topology.lean. Thus all hypotheses of UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty in Mathlib/NumberTheory/ModularForms/QExpansion.lean hold, with positive period N. Its conclusion is u=O[atImInfty](z↦exp(−2π Im z/N)). Expanding this Big-O statement and the height-filter basis yields real C≥0 and Y such that |u(z)|≤C exp(−a Im z) whenever Im z≥Y, where a=2π/N>0. A nonnegative C may be obtained by replacing any bound constant by its absolute value.
4. Apply the sibling p02_es_177ebb5a_sm_transformed_integral to n, the underlying function of f, E, σ, and the assumed IsEichlerIntegral proof. It gives IsEichlerIntegral n u G with exactly the functions defined in step 2.
5. For every z∈ℍ, exact equivariance under γ gives G(T_Nz)=ρ(σ⁻¹)E(σT_Nz)=ρ(σ⁻¹)E(γσz)=ρ(σ⁻¹)ρ(γ)E(σz). Since σ⁻¹γ=T_Nσ⁻¹ and ρ is a representation, this equals ρ(T_N)G(z). Thus G satisfies the exact translation-equivariance hypothesis of the sibling p02_es_177ebb5a_sm_translation_bound.
6. Apply p02_es_177ebb5a_sm_translation_bound using N≠0, continuity of u from step 3, its exponential bound from step 3, the integral predicate from step 4, and equivariance from step 5. This proves boundedness at imaginary infinity of z↦G(z)(1,−z). The sibling p02_es_177ebb5a_sm_slash, applied to n,E,σ and each z, identifies that scalarization with p|_{−n}σ. Hence this slash translate is bounded at imaginary infinity.
7. Let g=mapGL ℝ σ. By its selection in step 1, g•∞=c. The integral and real-matrix slash actions agree by ModularForm.SL_slash. Apply OnePoint.isBoundedAt_iff in Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean to this equality g•∞=c and the bound from step 6. Its conclusion is OnePoint.IsBoundedAt c p (−n), whose definition quantifies over every real scaling matrix sending infinity to c. Since c was an arbitrary cusp of the prescribed image ΓR, this proves the exact statement.

## Key steps

1. Obtain arithmeticity from the finite index of Γ₀(N) and represent the cusp by an integral scaling matrix.
2. Use normality of Γ(N) to obtain a conjugated translation in Γ₀(N).
3. Prove periodicity, holomorphy, and vanishing at infinity of the slash-translated cusp form.
4. Apply the pinned exponential-decay theorem with all its hypotheses checked.
5. Use integral covariance and exact equivariance to prepare the transformed primitive.
6. Apply the translation bound and scalar slash covariance.
7. Apply the single-scaling-matrix criterion to obtain the full bounded-at-cusp predicate.

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
