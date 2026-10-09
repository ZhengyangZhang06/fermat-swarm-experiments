<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1 -->

## Theorem `Submission.f036cc6b1f_pc_integral_core`

Let Δ be a finite-index subgroup of SL₂(ℤ) containing −I, regarded in GL₂(ℝ) by the canonical embedding. Put V=CuspForm Δ 2, μ=dx dy/y², and P(f,g)(z)=conjugate(f(z))g(z)(Im z)². There exists B : InnerProductSpace.Core ℂ V such that the following holds for every measurable F⊂ℍ: if for μ-almost every z there is γ∈Δ with γz∈F and every δ∈Δ with δz∈F satisfies δ=γ or δ=−γ, then, for every f,g∈V, P(f,g) is integrable on F and B.inner f g=∫_F P(f,g)dμ. The same B works for every such F.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/24

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/31

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/199, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/200, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/201

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_integral_core`

```lean
∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Δ.FiniteIndex], (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → ∃ B : InnerProductSpace.Core ℂ (CuspForm Δ 2), ∀ (F : Set UpperHalfPlane), MeasurableSet F → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) → ∀ f g : CuspForm Δ 2, MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 f g) F (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) ∧ B.inner f g = MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F) (UpperHalfPlane.petersson 2 f g)
```

### Frozen project context

`Fermat/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean` at `61b5f85556ac71631ccad822e0694511234f7132` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Δ as in the statement. Apply effective_domain to obtain a finite set R and a measurable domain E=⋃_{r∈R}rF₀ satisfying its almost-everywhere representative property. All integrations below use the canonical hyperbolic measure μ, without an index normalization.
2. For every σ∈SL₂(ℤ), the conjugate σ⁻¹Δσ has finite index. Among sufficiently many nonnegative powers of T=((1,1),(0,1)), two belong to the same right coset of this subgroup. Taking their quotient gives T^h∈σ⁻¹Δσ for some integer h>0. Thus σ∞ is a cusp of Δ, and, for any f∈V, f|₂σ is h-periodic and tends to zero as the imaginary part tends to infinity. Every rational boundary point, including infinity, has the form σ∞: a primitive integer pair representing it can be completed to a determinant-one matrix by Bézout's identity.
3. Fix r∈R and write u=f|₂r. It is holomorphic, has a positive period h as above, and tends to zero at infinity. The map q=exp(2πiz/h) identifies the quotient by this period with the punctured unit disk. Periodicity makes u descend to a holomorphic function there. Its zero limit supplies boundedness near zero, so the removable-singularity theorem extends it holomorphically with value zero. Write the extension as qU(q), where U is holomorphic. On any smaller closed disk U is bounded. Consequently there are C,Y with |u(x+iy)|≤C exp(−2πy/h) for all y≥Y, uniformly in x. Applying the same reasoning to v=g|₂r gives a common threshold and an exponentially decaying bound for |uv|. This is the cusp-decay argument formalized in the pinned QExpansion.lean.
4. The weight-two slash formula is (f|₂A)(z)=det(A)(cz+d)⁻²f(Az) for positive-determinant A. Substituting Im(Az)=det(A)Im(z)/|cz+d|² gives P(f|₂A,g|₂A)(z)=P(f,g)(Az). Together with preservation of μ, this shows that the integral of |P(f,g)| on rF₀ equals the planar integral of |(f|₂r)(z)(g|₂r)(z)| on F₀. The high part is bounded by C′exp(−ay), with a>0 and horizontal width at most one, so its integral is finite. Choose the height threshold at least one. The remaining part of F₀ is contained in the compact set |x|≤1/2 and √3/2≤y≤Y; continuity bounds the integrand there. Hence P(f,g) is integrable on each rF₀ and therefore on E. Its measurability follows from continuity.
5. Slash invariance of f and g and the covariance identity imply that P(f,g) is Δ-invariant. Now let F be any measurable set satisfying the representative hypothesis. The exceptional sets for the representative properties of E and F are measurable and null: their predicates involve only countably many measurable translates. Remove their countable Δ-saturations. The remaining set X is measurable, conull, and Δ-invariant, and both representative properties hold at every point of X.
6. Choose a countable set L of representatives of Δ/{±I}. The sets E∩X∩γF, for γ∈L, partition E∩X. Coverage follows from the representative property of F, and disjointness follows from uniqueness modulo ±I. Translating each piece by γ⁻¹ gives F∩X∩γ⁻¹E; these partition F∩X by the property of E. Invariance of μ and P first gives equality of the nonnegative absolute integrals on the two partitions. Thus ∫_F|P(f,g)|dμ=∫_E|P(f,g)|dμ<∞. Countable additivity for the now absolutely integrable complex function gives ∫_F P(f,g)dμ=∫_E P(f,g)dμ.
7. Define B(f,g)=∫_E P(f,g)dμ. Step 4 ensures integrability for every pair, including sums and scalar multiples. The pointwise identities P(f₁+f₂,g)=P(f₁,g)+P(f₂,g), P(cf,g)=conjugate(c)P(f,g), and P(g,f)=conjugate(P(f,g)) therefore pass through the integral. They give additivity, conjugate-linearity in the first variable, and conjugate symmetry. In particular, B is linear in the second variable.
8. The diagonal integrand P(f,f)(z)=|f(z)|²(Im z)² is real and nonnegative. Its integral has nonnegative real part. If B(f,f)=0, the integral of this nonnegative real function is zero, so it vanishes μ-almost everywhere on E. Its Δ-invariance and countability of Δ extend this vanishing to almost every point of ⋃_{γ∈Δ}γE. The representative property of E makes this union conull, so the diagonal integrand vanishes almost everywhere on ℍ.
9. If f(z₀) were nonzero, continuity would give an open disk U about z₀, with closure inside ℍ, and ε>0 such that |f(z)|²(Im z)²≥ε on U. The imaginary coordinate is bounded above on U, so the density y⁻² has a strictly positive lower bound there. Since an open disk has positive planar area, μ(U)>0. This contradicts the almost-everywhere vanishing. Therefore f vanishes pointwise, and extensionality gives f=0 in V.
10. Steps 7–9 supply exactly the conjugate symmetry, nonnegative real diagonal, additivity, conjugate scalar law, and definiteness fields of InnerProductSpace.Core. Construct B with inner product given by the integral over E. For every admissible F, step 6 supplies both the stated integrability and the identity B.inner f g=∫_F P(f,g)dμ. Since E and B were fixed before F, one Core works for all such domains.

## Key steps

1. Obtain a finite union of modular-domain translates from effective_domain.
2. Use finite-index cusp widths and the punctured-disk coordinate to establish uniform exponential cusp decay.
3. Combine Petersson covariance with cusp decay and compactness to prove absolute integrability.
4. Partition two domains using Δ/{±I} to prove integrability transfer and domain independence.
5. Pass the sesquilinear and conjugate-symmetry identities through the integral.
6. Use nonnegativity, almost-everywhere coverage, continuity, and positive measure of open disks to prove definiteness.
7. Construct one Core representing the integral on every admissible domain.

## Reference use

### local-project

Queries:
- `rg --files .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb -g '*.lean' -g '*json' -g 'lean-toolchain' -g 'lakefile*'`
- `grep -R -n -E 'petersson|Petersson|InnerProductSpace.Core|IsFundamentalDomain' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `grep -R -n -E 'IsFundamentalDomain|integrable.*petersson|petersson.*integrable|heckeTLin.*[Ss]ymmet|[Ss]ymmet.*heckeTLin' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `grep -R -n -E 'f036cc6b1f_pc_effective_domain|f036cc6b1f_pc_integral_core|f036cc6b1f_pc_hecke_integral' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json Submission.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `python3 /tmp/f036cc6b1f_petersson_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperator.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean`
- `/tmp/f036cc6b1f_petersson_contracts/CheckTypes.lean`
- `/tmp/f036cc6b1f_petersson_contracts/CheckTypes.log`
- `/tmp/f036cc6b1f_petersson_contracts/CheckInstances.log`
- `/tmp/f036cc6b1f_petersson_contracts/CheckCoreProjection.log`
- `/tmp/f036cc6b1f_petersson_contracts/CheckAxioms.log`
- `/tmp/f036cc6b1f_petersson_contracts/Submission.log`
- `/tmp/f036cc6b1f_petersson_contracts/ImportSubmissionCheck.log`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib matches that revision and has clean status; all compiled local dependency sources match the snapshot byte-for-byte. The attempted rg command failed because rg is unavailable, so searches used grep. No existing integrated fundamental-domain/Petersson-integrability/Hecke-symmetry result was found in the searched directories, and the proposed identifiers have no active-DAG collisions. The inspected sources supply modular-domain covering and interior uniqueness, cusp decay, Petersson covariance, hyperbolic measure invariance, the exact Hecke normalization, and Core fields. All three proposed types elaborate against Definitions.Def_ModularForm_HeckeOperatorForms with the project’s Lean options. Instance checks confirm UpperHalfPlane.instMeasureSpace, the SL action, the GL-invariant hyperbolic measure, and projection of the existential B in B.inner. Nine audited library declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. However, the required literal import Submission gate remains blocked: unchanged Submission.lean fails on the missing attribute targets FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions and FreyPackage.ModMCarrier.coe_rescaleLin_apply. No project source was modified; this is not comparator acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/680

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
