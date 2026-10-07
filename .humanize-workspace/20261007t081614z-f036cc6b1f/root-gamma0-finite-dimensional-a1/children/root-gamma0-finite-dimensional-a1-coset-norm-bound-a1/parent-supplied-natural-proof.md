# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_finite_dimensional-a1`
- Child DAG node: `root.gamma0_finite_dimensional-a1.coset_norm_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix M ≠ 0 and f. Let Γ be the image of Γ₀(M) in H, the image of SL₂(ℤ). The principal congruence subgroup Γ(M) is the kernel of reduction to the finite group SL₂(ℤ/Mℤ), and Γ(M) is contained in Γ₀(M). Hence Γ₀(M) has finite index, as also established by CongruenceSubgroup.instFiniteIndexGamma0. The injective map from SL₂(ℤ) onto H identifies the corresponding coset spaces, so Q = H / (Γ.subgroupOf H) is finite and nonempty.
2. The definition of ModularForm.norm in the pinned NormTrace.lean is N(f)(z) = ∏_(q∈Q) SlashInvariantForm.quotientFunc f q z. For each q choose a representative r_q in H and lift it to σ_q in SL₂(ℤ). The corresponding factor is h_q = f|₂σ_q⁻¹. For the identity coset q₀ choose r_q₀ = 1 and σ_q₀ = 1; then h_q₀ = f. The definition of quotientFunc makes these factors independent of the representative choices.
3. Let T be the integral translation matrix with upper-right entry 1. Since M ≠ 0, T^M is a noncentral parabolic element of Γ(M). Normality of Γ(M) implies σ_q⁻¹T^Mσ_q ∈ Γ(M) ⊆ Γ₀(M). This conjugate fixes σ_q⁻¹∞ and remains noncentral and parabolic. Thus σ_q⁻¹∞ is a cusp of Γ₀(M).
4. Apply the defining cusp condition of f at σ_q⁻¹∞, using σ_q⁻¹ as the translating matrix. It states that h_q tends to zero as the imaginary part tends to infinity. In particular, for each q ≠ q₀ there is a real Y_q such that ‖h_q(z)‖ ≤ 1 whenever Im z ≥ Y_q. This bound is uniform in the real part, since the filter is UpperHalfPlane.atImInfty.
5. The set Q excluding q₀ is finite. Choose Y at least every Y_q; if that set is empty, take Y = 0. For Im z ≥ Y, multiplicativity of the complex norm and the product formula give ‖N(f)(z)‖ = ‖f(z)‖ ∏_(q≠q₀) ‖h_q(z)‖ ≤ ‖f(z)‖. The empty-product case satisfies the same identity and inequality.
6. Take C = 1. Then C ≥ 0 and the inequality in the statement holds for every z with Im z ≥ Y, establishing all required conclusions.

## Key steps

1. Use principal-congruence containment to make the norm's coset space finite.
2. Expand the existing norm as its defining product and select the identity factor.
3. Use conjugates of T^M to identify the cusp associated with every remaining factor.
4. Bound each remaining translated cusp form by 1 above a common height.
5. Multiply the bounds and choose C = 1.

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
