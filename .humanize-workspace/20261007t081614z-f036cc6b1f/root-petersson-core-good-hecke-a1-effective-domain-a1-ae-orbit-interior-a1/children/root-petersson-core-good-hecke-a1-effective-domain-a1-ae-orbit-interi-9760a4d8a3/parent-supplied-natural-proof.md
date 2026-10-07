# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1.measurable_null_orbit_avoidance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a measurable set S ⊆ ℍ with μ(S) = 0. For each a ∈ G, define Tₐ(z) = a • z and Bₐ = Tₐ⁻¹(S).
2. Let g be the image of a under Matrix.SpecialLinearGroup.mapGL ℝ. By the definition UpperHalfPlane.SLAction in the pinned MoebiusAction.lean, Tₐ(z) = g • z. The GL₂(ℝ) action maps are continuous by UpperHalfPlane.instContinuousGLSMul, so Tₐ is measurable and Bₐ is measurable. The invariant-measure instance in UpperHalfPlane/Measure.lean states that the GL₂(ℝ) action preserves hyperbolic measure. Applying its measurable-preimage identity to g and S gives μ(Bₐ) = μ(S) = 0.
3. The map sending a ∈ SL₂(ℤ) to its four integer matrix entries is injective, since equality of all entries implies equality of matrices and hence equality in the determinant-one subtype. A finite product of countable sets is countable, so ℤ⁴ is countable and therefore G is countable. In the pinned definitions, this is precisely the determinant-one subtype of the function space Fin 2 → Fin 2 → ℤ.
4. Define N = ⋃ₐ∈G Bₐ. This is a countable union of measurable sets, so it is measurable. Countable subadditivity and step 2 give μ(N) ≤ Σₐ∈G μ(Bₐ) = 0. Nonnegativity then yields μ(N) = 0.
5. If z ∉ N, then z ∉ Bₐ for every a ∈ G. By the definition of Bₐ, this means a • z ∉ S for every a. Since N has measure zero, its complement has full μ-measure, proving the required simultaneous almost-everywhere assertion.

## Key steps

1. Form the preimage of the prescribed null set under each modular action map.
2. Restrict GL₂(ℝ) continuity and measure invariance to show every preimage is measurable and null.
3. Prove SL₂(ℤ) countable through its four integer entries.
4. Remove the countable union of all preimages.
5. Read nonmembership in that union as avoidance by every modular translate.

## Reference use

### local-project

Queries:
- `isClosed_fd|isOpen_fdo|def fd|def fdo|volume|measure|ae_|boundary`
- `SLAction|mapGL|instContinuousGLSMul|continuous.*smul|smul_eq`
- `fd.*fdo|fdo.*fd|boundary.*(null|zero)|volume.*fd|fd.*volume`
- `measure_prod_null_of_ae_null|volume_preserving_equiv_real_prod|measure_preimage_fst|measure_sphere|sphere.*zero`
- `measure_preimage_smul|measurePreserving_smul|ae_smul|quasiMeasurePreserving_smul`
- `ae_all_iff|ae_iff|theorem ae_notMem`
- `structure SpecialLinearGroup|def SpecialLinearGroup|val_injective|coe_injective|theorem ext|lemma ext|Countable`
- `f036cc6b1f_pc_ed_aoi_boundary_null|f036cc6b1f_pc_ed_aoi_null_orbit`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `#synth MeasureTheory.MeasureSpace UpperHalfPlane`
- `#synth SMul (Matrix.SpecialLinearGroup (Fin 2) ℤ) UpperHalfPlane`
- `#check (inferInstanceAs (Countable { A : Fin 2 → Fin 2 → ℤ // Matrix.det A = 1 }) : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ))`
- `#print axioms UpperHalfPlane.volume_eq_lintegral`
- `#print axioms UpperHalfPlane.instSMulInvariantMeasureGeneralLinearGroupFinOfNatNatRealVolume`
- `#print axioms MeasureTheory.Measure.measure_prod_null_of_ae_null`
- `#print axioms Complex.volume_preserving_equiv_real_prod`
- `#print axioms MeasureTheory.ae_all_iff`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/Action.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Data/Countable/Defs.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/P2M`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-ae-orbit-interior-a1/decomposition-checks-v1/FrozenTypesFinal.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-ae-orbit-interior-a1/decomposition-checks-v1/FrozenTypesFinal.log`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-ae-orbit-interior-a1/decomposition-checks-v1/CompatibilityFinal.json`

The snapshot pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Modular.lean supplies the exact domain definitions and their closed/open properties. Measure.lean supplies the hyperbolic density formula and GL₂(ℝ) invariance; MoebiusAction.lean and Topology.lean identify the restricted SL₂(ℤ) action and its continuity. Prod.lean and Lebesgue/Complex.lean justify planar nullness through null sections and the measure-preserving real-coordinate identification. Group/Action.lean and OuterMeasure/AE.lean supply invariant preimages and countable almost-everywhere quantification. The targeted search in project/Definitions and project/P2M found no boundary-null helper. Neither proposed identifier occurs in the active DAG or searched declarations. Both frozen child expressions elaborate through literal import Submission; the final check exits 0. Instance inspection confirms the hyperbolic MeasureSpace and UpperHalfPlane.SLAction. Countability requires explicitly unfolding both SpecialLinearGroup and Matrix; its witness also checks. All nine installed dependencies are clean and pinned; twenty project sources and eight mathlib sources were checked against the recorded snapshot. The thirteen audited infrastructure declarations use only propext, Classical.choice, Quot.sound, or no axioms. These are compatibility checks, not comparator acceptance of either proposed theorem.
