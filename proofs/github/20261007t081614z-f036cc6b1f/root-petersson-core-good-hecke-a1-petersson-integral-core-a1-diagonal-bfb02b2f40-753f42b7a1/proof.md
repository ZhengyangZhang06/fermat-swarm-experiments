# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.diagonal_integral_definite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Δ,E,f as stated and define A(z)=|f(z)|²(Im z)², a real-valued continuous nonnegative function. The identity conjugate(f(z))f(z)=|f(z)|² identifies P(f,f)(z) with the complex image of A(z). Taking real parts is a continuous real-linear map, so the assumed integrability gives integrability of A on E and ∫_E A dμ=Re(∫_E P(f,f)dμ)=0.
2. A nonnegative integrable real function with zero integral vanishes almost everywhere. Hence N=E∩{z : A(z)≠0} is measurable and μ-null; measurability follows from measurability of E and continuity of A.
3. The diagonal is Δ-invariant. For γ∈Δ the slash-invariance of f, together with the determinant-one Petersson covariance identity, gives P(f,f)(γz)=P(f,f)(z), and taking real parts gives A(γz)=A(z). Every γ acts by a μ-preserving homeomorphism. The group Δ is countable as a subgroup of the integer matrices, so N*=⋃_{γ∈Δ}γ⁻¹N is measurable and null.
4. Put C=⋃_{γ∈Δ}γ⁻¹E. The coverage hypothesis states precisely that C is conull, and countability makes it measurable. If z∈C\N*, choose γ∈Δ with γz∈E. Since z∉γ⁻¹N, we have γz∉N, so A(γz)=0. Invariance implies A(z)=0. Thus A vanishes μ-almost everywhere on all of ℍ.
5. Suppose f(z₀)≠0 for some z₀=x₀+iy₀∈ℍ. Then A(z₀)>0. By continuity choose a Euclidean disk U of radius r>0 centered at z₀, with r<y₀/2 and A(z)≥A(z₀)/2 on U. It is a measurable open subset of ℍ whose closure stays in ℍ. On U we have y≤y₀+r, so the hyperbolic density satisfies y⁻²≥(y₀+r)⁻². The disk has planar area πr²>0; consequently μ(U)≥πr²/(y₀+r)²>0. This contradicts step 4, since A is strictly positive at every point of U.
6. Therefore f(z)=0 for every z∈ℍ. The zero cusp form has the same underlying function, and extensionality of cusp forms gives f=0.

## Key steps

1. Identify the complex diagonal with the real nonnegative continuous function |f|²(Im z)².
2. Use zero integral and nonnegativity to obtain almost-everywhere vanishing on E.
3. Establish subgroup invariance and saturate the null exceptional set.
4. Use almost-everywhere orbit coverage to propagate vanishing to ℍ.
5. Contradict any nonzero value using continuity and positive hyperbolic measure of a small disk.
6. Apply cusp-form extensionality.

## Reference use

### local-project

Queries:
- `rg -n 'integrable.*petersson|petersson.*integrable|integral.*petersson|petersson.*integral|IsOpenPosMeasure' project/Definitions mathlib/Mathlib/NumberTheory/ModularForms mathlib/Mathlib/Analysis/Complex/UpperHalfPlane`
- `exp_decay|cuspFunction|hasSum|zero_at|IsCusp|FiniteIndex|translate`
- `def fd|def fdo|isClosed_fd|sqrt|im.*fd|mem_fd`
- `SL_neg_smul|coeSubgroup|coe.*Subgroup|instCoe`
- `f036cc6b1f_pic_translated_integrable|f036cc6b1f_pic_domain_transfer|f036cc6b1f_pic_diagonal_definite`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `python3 /tmp/f036cc6b1f_integral_core_split/verify.py`
- `tail -8 /tmp/f036cc6b1f_integral_core_split/CheckInfrastructure.log`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean`
- `/tmp/f036cc6b1f_integral_core_split/verify.py`
- `/tmp/f036cc6b1f_integral_core_split/CheckTypes.lean`
- `/tmp/f036cc6b1f_integral_core_split/CheckTypes.log`
- `/tmp/f036cc6b1f_integral_core_split/CheckInfrastructure.lean`
- `/tmp/f036cc6b1f_integral_core_split/CheckInfrastructure.log`

The snapshot pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. All nine installed package revisions match their pins and have clean working trees. The inspected mathlib sources and all twenty local dependency modules rebuilt for this check match the snapshot. QExpansion.lean supplies the removable-singularity and exponential-decay arguments; Petersson.lean supplies continuity and covariance; Measure.lean defines the unnormalized hyperbolic measure and proves GL₂(ℝ)-invariance; Modular.lean supplies the domain geometry. The targeted search found no matching Petersson-integrability/integral or IsOpenPosMeasure declarations in the searched directories. All three proposed types elaborate after literal import Submission. Instance inspection confirms UpperHalfPlane.instMeasureSpace, UpperHalfPlane.SLAction.toSMul, matrix multiplication in GL₂(ℝ), and the subgroup embedding Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ). Twelve audited infrastructure declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. The proposed names have no active-DAG collisions. These checks establish interface compatibility, not comparator acceptance of the proposed child proofs.
