# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_finite_dimensional-a1`
- Child DAG node: `root.gamma0_finite_dimensional-a1.gamma0_sturm_vanishing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix M ≠ 0, f, and the coefficient-vanishing hypothesis. Let d = (CongruenceSubgroup.Gamma0 M).index and b = (2d)/12, using natural-number division. Finite index follows from CongruenceSubgroup.instFiniteIndexGamma0. The integral translation T belongs to Γ₀(M), so 1 is a strict period of its image in GL₂(ℝ). Regard f as a modular form using ModularFormClass.modularForm; this preserves its underlying function and q-expansion.
2. Apply coeff_vanishing_iff_decay to this modular form and b. The hypothesis supplies constants C_f ≥ 0 and Y_f such that ‖f(z)‖ ≤ C_f exp(−2π(b+1) Im z) whenever Im z ≥ Y_f.
3. Let H be the image of SL₂(ℤ) in GL₂(ℝ), and let N = ModularForm.norm H f. The pinned NormTrace.lean constructs N as a modular form for H of weight 2·Nat.card Q, where Q = H / ((Γ₀(M) mapped into GL₂(ℝ)).subgroupOf H). The injective homomorphism SL₂(ℤ) → H is surjective onto H and takes Γ₀(M) onto that subgroup. It therefore induces a bijection SL₂(ℤ)/Γ₀(M) → Q: a coset represented by σ maps to the coset represented by its image; equality of either pair of cosets is equivalent to membership of the representative quotient in Γ₀(M). Consequently Nat.card Q = d. Thus N has the natural weight K = 2d, viewed as an integer.
4. Apply coset_norm_bound to obtain C_N ≥ 0 and Y_N with ‖N(z)‖ ≤ C_N‖f(z)‖ whenever Im z ≥ Y_N. For Im z ≥ max(Y_f,Y_N), multiplying the estimate from step 2 by the nonnegative C_N gives ‖N(z)‖ ≤ (C_N C_f) exp(−2π(b+1) Im z), with C_N C_f ≥ 0.
5. The full modular group H has strict period 1. Apply the reverse implication of coeff_vanishing_iff_decay to N and the bound from step 4. Every coefficient of UpperHalfPlane.qExpansion 1 N of degree at most b is zero.
6. Hence the order of this power series is greater than b. Indeed, if the series is zero its order is infinity; otherwise its order is the least degree with nonzero coefficient, and step 5 excludes every degree at most b. Since b = K/12, this is exactly the hypothesis of ModularForm.sturm_bound_levelOne_nat in the pinned LevelOne/DimensionFormula.lean. That theorem gives N = 0.
7. Apply ModularForm.norm_eq_zero_iff from the pinned NormTrace.lean. It converts N = 0 into the assertion that the underlying function of f is zero. Extensionality of cusp forms then gives f = 0, as required.

## Key steps

1. Obtain strict period 1 and exponential decay from the assumed coefficient vanishing.
2. Use the existing norm and identify its quotient cardinality with the integral subgroup index.
3. Combine norm domination with the decay estimate.
4. Convert the resulting norm decay back into vanishing coefficients.
5. Apply the level-one Sturm bound at natural weight twice the index.
6. Use norm_eq_zero_iff and cusp-form extensionality.

## Reference use

### local-project

Queries:
- `rg -n 'ModularForm.norm|norm_eq_zero_iff|sturm_bound_levelOne_nat|hasSum_qExpansion|instFiniteIndexGamma0' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb`
- `grep -R -n -E 'sturm_bound_levelOne_nat|hasSum_qExpansion|qExpansion_coeff_unique|instFiniteIndexGamma0|finiteDimensional|FiniteDimensional' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `grep -R -n -E 'isBigO.*norm|norm.*isBigO|coeff.*exp|exp.*coeff|order.*isBigO|isBigO.*order' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `#print axioms ModularForm.norm`
- `#print axioms ModularForm.norm_eq_zero_iff`
- `#print axioms ModularForm.sturm_bound_levelOne_nat`
- `#print axioms UpperHalfPlane.hasSum_qExpansion`
- `#print axioms CongruenceSubgroup.instFiniteIndexGamma0`
- `#print axioms FiniteDimensional.of_injective`
- `#print axioms ModularFormClass.analyticAt_cuspFunction_zero`
- `#print axioms ModularForm.qExpansion_add`
- `#print axioms ModularForm.qExpansion_smul`
- `#print axioms ModularFormClass.modularForm`
- `Python scan of dag.json and nodes/**/*.json for f036cc6b1f_fd_coeff_decay, f036cc6b1f_fd_norm_bound, and f036cc6b1f_fd_sturm`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-gamma0-finite-dimensional-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/NormTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/GroupTheory/Index.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/Submission.lean`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckDependencyTypes.lean`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckDependencyTypes.log`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckNormInstances.lean`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckNormInstances.log`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/Submission.log`
- `/tmp/fermat_p01_fd_decomp_s1ak2yew/CheckSubmission.log`

The snapshot pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib has that revision and clean status; the inspected library files and all 20 compiled project dependencies match the snapshot byte-for-byte. The requested rg command was attempted, but rg is unavailable; grep and Python supplied the searches. NormTrace.lean already provides ModularForm.norm and ModularForm.norm_eq_zero_iff, eliminating separate construction and nonvanishing obligations. QExpansion.lean supplies the analytic disk function, convergent expansion, and coefficient linearity; DimensionFormula.lean supplies the exact level-one Sturm bound. No matching Gamma0 finite-dimensionality theorem or norm-domination theorem was found in the searched directories. All ten audited declarations use only propext, Classical.choice, and Quot.sound. The three proposed types elaborate under the actual Definitions.Def_ModularForm_HeckeOperatorForms import. Separate checks verify the norm's inferred finite-relative-index, determinant, and modular-form instances, its weight, and its defining finite product. No proposed identifier occurs in the active DAG or handoffs. However, literal import Submission validation is blocked: unchanged Submission.lean fails on unknown constants FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions and FreyPackage.ModMCarrier.coe_rescaleLin_apply. These proposed children must not activate until that required import gate passes. No proof acceptance is claimed.
