# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_parabolic-a1`
- Child DAG node: `root.primitive_parabolic-a1.integral_parabolic_normal_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix γ∈SL₂(ℤ) with t=tr(γ) and t²=4. Factoring gives (t−2)(t+2)=0. Since ℤ is an integral domain, t=2 or t=−2. Choose ε∈{1,−1} with t=2ε; then ε²=1.
2. If γ=εI, choose σ=I and m=0. Since T^0=I, the first disjunct holds when ε=1 and the second when ε=−1. Hence assume γ≠εI, and set M=γ−εI. The two-by-two determinant formula gives det M=det γ−ε tr γ+ε²=1−2ε²+ε²=0, while M≠0.
3. Produce a nonzero integral vector in the kernel of M explicitly. Write M=(a b;c d). If its first row is nonzero, take v=(b,−a). Its first image coordinate is ab−ba=0, and its second is cb−da=−det M=0. The vector is nonzero because the first row is nonzero. If the first row is zero, the second row is nonzero, and v=(d,−c) is nonzero and has image zero. Thus in either case Mv=0 with v∈ℤ² nonzero.
4. Let g be the positive greatest common divisor of the two coordinates of v. Divide them by g to obtain integers p,q with v=g(p,q) and gcd(|p|,|q|)=1. Cancelling the nonzero integer g from Mv=0 gives M(p,q)=0, or γ(p,q)=ε(p,q). Bézout's identity supplies integers u,v₀ with up+v₀q=1. Set r=−v₀ and s=u. Then ps−qr=1.
5. Let σ be the integral matrix with columns (p,q) and (r,s). Its determinant is ps−qr=1, so σ∈SL₂(ℤ). Put δ=σ⁻¹γσ. Because the first column of σ is an ε-eigenvector of γ, the first column of δ is (ε,0). Thus δ has the form (ε b₀;0 d₀), with b₀,d₀ integers. Its determinant is one, so εd₀=1. Multiplying by ε and using ε²=1 yields d₀=ε.
6. Put m=εb₀. For every integer m, T^m=(1 m;0 1): positive powers follow by multiplying upper-unitriangular matrices, and negative powers follow from T⁻¹=(1 −1;0 1). Hence εT^m=(ε εm;0 ε)=(ε b₀;0 ε)=δ. If ε=1 this is δ=T^m; if ε=−1 it is δ=−T^m. These are exactly the required disjuncts.

## Key steps

1. Factor the trace equation to obtain trace 2ε with ε=±1.
2. Handle the central matrices and show γ−εI is singular in the remaining case.
3. Construct a nonzero integral kernel vector directly from a nonzero row.
4. Divide by the coordinate gcd and complete the primitive eigenvector using Bézout.
5. Conjugate into an upper-triangular matrix with both diagonal entries ε.
6. Identify the resulting matrix as T^m or −T^m for an integer m.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|IsEquivariantPrimitiveWith|IsParabolicCocycle|eichlerShimuraMap_injective|exp_decay_atImInfty`
- `isCusp|isZeroAt|zero_at|conj|slash|normal|strictPeriods`
- `trace.*(sq|\^ 2)|parabolic.*conjug|conjug.*parabolic|exists.*(T \^|T\^)`
- `coe_T_zpow|T_zpow|neg.*smul|smul.*neg|def ofComplex|ofComplex_apply`
- `rg -n 'p02_es_177ebb5a_pp_(scaled_cusp_decay|primitive_cusp_limit|integral_parabolic_normal_form)' Submission.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes`
- `git -C .lake/packages/mathlib status --short`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `cmp Definitions/Def_HeckeEis_EichlerIntegral.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `cmp Definitions/Def_HeckeEis_BinaryFormRep.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `cmp Definitions/Def_Gamma0CoeffCohomology.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_177ebb5a_pp_typecheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/tmp/p02_177ebb5a_pp_typecheck.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The installed mathlib matches that revision and has clean Git status; the three relevant project definition files match the snapshot byte-for-byte. Existing infrastructure supplies sub_eq_cocycle, binaryFormRepSL_linePow, jFactor_ne_zero, Gamma_normal, ModularGroup_T_pow_mem_Gamma, and cusp vanishing after slash. QExpansion.lean supplies exponential decay from positive periodicity, holomorphy, boundedness, and vanishing at imaginary infinity. The searched matrix, modular-form, and project-definition sources contain no matching integral conjugacy theorem covering every trace-squared-four matrix. The proposed identifiers have no matches in Submission or the DAG metadata. All three exact propositions elaborate after import Submission under Lean 4.33.1; additional checked equalities verify matrix multiplication and matrix negation for the inferred special-linear-group instances. Transitive axiom checks for the seven inspected reusable lemmas report only propext, Classical.choice, and Quot.sound. These checks validate the interfaces and reference reuse, not acceptance of new theorem proofs.
