# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.diagonal_integral_definite-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.diagonal_integral_definite-a1.hyperbolic_volume_open_positive-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let ν be planar Lebesgue measure pulled back along the inclusion ℍ→ℂ. By the definition of hyperbolic volume, μ=ν.withDensity(w), where w(z)=(Im z)⁻². This density is measurable and strictly positive at every point of ℍ.
2. Fix any nonempty open set U⊂ℍ and choose z₀=x₀+iy₀∈U. Here y₀>0. The inclusion ℍ→ℂ is an open embedding, so the image of U is open in ℂ. Choose ρ>0 such that the planar disk B(z₀,ρ) lies in that image, and set r=min(ρ/2,y₀/4). Then r>0, r<ρ, and r<y₀/2. The disk B(z₀,r) corresponds to a measurable open set V⊂U in ℍ.
3. For z∈V, the inequality |Im z−y₀|≤|z−z₀|<r gives 0<Im z<y₀+r. Hence w(z)≥c, where c=(y₀+r)⁻²>0.
4. The inclusion maps V bijectively onto B(z₀,r), and ν is pulled-back planar measure. Therefore ν(V)=πr²>0. The density formula and monotonicity of the nonnegative integral give μ(V)=∫_V w dν≥cν(V)=πr²/(y₀+r)²>0, with nonnegative real quantities viewed in the extended nonnegative reals.
5. Since V⊂U, monotonicity gives μ(U)≥μ(V)>0, so μ(U)≠0. This holds for every nonempty open U and is exactly Measure.IsOpenPosMeasure μ.

## Key steps

1. Express hyperbolic volume as planar measure weighted by (Im z)⁻².
2. Place a positive-radius planar disk inside an arbitrary nonempty open set.
3. Bound the density below by a strictly positive constant on that disk.
4. Combine positive disk area with the density bound to obtain positive hyperbolic volume.
5. Apply measure monotonicity to the original open set.

## Reference use

### local-project

Queries:
- `petersson_self|petersson.*nonneg|petersson.*zero|petersson.*invariant|theorem.*petersson|lemma.*petersson`
- `continuous.*ae_eq|eq_of_ae_eq|integral_eq_zero_iff_of_nonneg`
- `isOpenPosMeasure|IsOpenPosMeasure|ae_eq|ae.*withDensity|withDensity.*ae`
- `IsOpenPosMeasure.*UpperHalfPlane|UpperHalfPlane.*IsOpenPosMeasure|ae.*orbit|orbit.*ae|ae_orbit_zero|dd_open_pos`
- `ae_.*smul|measurePreserving_smul|preimage_smul|ae_all_iff`
- `f036cc6b1f_pic_dd_ae_orbit_zero|f036cc6b1f_pic_dd_open_pos`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/Action.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-diagonal-bfb02b2f40/decomposition-typechecks-dd/FrozenTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-diagonal-bfb02b2f40/decomposition-typechecks-dd/FrozenTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-diagonal-bfb02b2f40/decomposition-typechecks-dd/Compatibility.json`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Petersson.lean supplies continuity and determinant-one invariance; Bochner/Basic.lean supplies the nonnegative zero-integral criterion; OpenPos.lean supplies equality of continuous functions from almost-everywhere equality once full support is established. UpperHalfPlane/Measure.lean supplies the hyperbolic density and GL₂(ℝ)-invariance. Searches found no existing theorem with the proposed orbit-cover propagation statement and no hyperbolic full-support declaration in the snapshot; the latter name occurs only in cleanup commands. Both proposed names are unreserved in the current DAG. All nine installed packages are clean and pinned, and the relevant mathlib sources and twenty local import sources match the snapshot. Both exact child types elaborate after import Submission under Lean 4.33.1. Instance inspection confirms hyperbolic volume and the canonical SL₂ action through mapGL. Thirteen inspected infrastructure declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. These checks validate the proposed interfaces, not acceptance of future child proofs.
