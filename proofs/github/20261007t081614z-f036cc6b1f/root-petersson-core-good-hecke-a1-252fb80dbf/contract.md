<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1 -->

## Theorem `Submission.f036cc6b1f_petersson_core`

For every natural number M with M ≠ 0, let V = CuspForm (CongruenceSubgroup.Gamma0 M) 2 with its existing complex vector space structure. There exists an InnerProductSpace.Core ℂ V, namely a positive-definite Hermitian form B conjugate-linear in its first variable, such that for every natural prime p not dividing M, every corresponding proof witnesses hp and hpM, and every f,g ∈ V, B(CuspForm.heckeTLin 2 hp hpM f,g) = B(f,CuspForm.heckeTLin 2 hp hpM g). The same B works for all such primes.

Node: `root.petersson_core_good_hecke-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/31, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/32, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/33

## Lean problem

Declaration: `Submission.f036cc6b1f_petersson_core`

```lean
∀ (M : ℕ) [NeZero M], ∃ B : InnerProductSpace.Core ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2), ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) (f g : CuspForm (CongruenceSubgroup.Gamma0 M) 2), B.inner (CuspForm.heckeTLin 2 hp hpM f) g = B.inner f (CuspForm.heckeTLin 2 hp hpM g)
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

- Parent DAG node: `root`
- Child DAG node: `root.petersson_core_good_hecke-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix M ≠ 0 and put Γ = Γ₀(M). The kernel Γ(M) of reduction modulo M is normal, has finite index in SL₂(ℤ), and is contained in Γ. Thus Γ has finite index; it also contains −I. More generally, if Δ has finite index in SL₂(ℤ), then σ⁻¹Δσ contains T^h for some positive integer h, for every σ ∈ SL₂(ℤ): two nonnegative powers of T have the same coset, and their quotient supplies a nonzero power. Hence every rational point σ∞ is a cusp. Conversely, the repeated-root fixed-point equation of a noncentral integer parabolic has a rational solution or the solution infinity. Thus these groups have precisely the rational cusps.
2. For a positive-determinant real matrix A = ((a,b),(c,d)), the frozen weight-two slash formula is (u|₂A)(z) = det(A)(cz+d)⁻²u(Az). The denominator cocycle and multiplicativity of determinants give (u|₂A)|₂B = u|₂(AB). Positive scalar matrices act trivially, since their determinant factor t² cancels the denominator factor t². Put P(u,v)(z) = conjugate(u(z))v(z)(Im z)² and dμ = dx dy/(Im z)². The identity Im(Az) = det(A)Im(z)/|cz+d|² gives P(u|₂A,v|₂A)(z) = P(u,v)(Az). The real Jacobian det(A)²/|cz+d|⁴ cancels the corresponding change in the square of the imaginary coordinate, so A preserves μ. These agree with the pinned UpperHalfPlane.petersson_slash and the invariant-measure result in UpperHalfPlane/Measure.lean.
3. If u is a cusp form for a finite-index subgroup Δ and r ∈ SL₂(ℤ), then u|₂r is holomorphic, periodic with some positive integer period h by step 1, and tends to zero at infinity by cuspidality at r∞. Under q = exp(2πiz/h), periodicity defines a holomorphic function on the punctured disk. Boundedness removes the singularity, and the zero limit makes its constant coefficient zero. Dividing its Taylor series by q gives a holomorphic function bounded on a smaller closed disk. Consequently |(u|₂r)(x+iy)| ≤ C exp(−2πy/h) for large y, uniformly in x. This is also supplied by the cusp-function theory in the pinned QExpansion.lean.
4. For a finite-index Δ containing −I, take F₀ = {x+iy : |x| ≤ 1/2, x²+y² ≥ 1, y > 0}, and let F_Δ be the union of rF₀ over representatives of Δ\SL₂(ℤ). The covering theorem ModularGroup.exists_smul_mem_fd and uniqueness theorem ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd in the pinned Modular.lean show that this is a fundamental domain up to boundaries for the effective action modulo {±I}. Indeed, equality between interior representatives forces the relating full-group matrix to be ±I, and these matrices belong to Δ. The boundary of F₀ consists of line and circle arcs. Such arcs have planar area zero, as do their Möbius images, by local smoothness; the density y⁻² is locally bounded on the upper half-plane, so these sets also have μ-measure zero. Countably many translates still have null union. All these domains and pieces are measurable.
5. For weight-two cusp forms u,v on Δ, the integral of |P(u,v)| over a piece rF₀ transforms, by step 2, into the planar integral of |(u|₂r)(z)(v|₂r)(z)| over F₀. On its high part step 3 bounds the integrand by C exp(−ay) for some a > 0. Its horizontal width is at most one, and ∫_Y^∞ exp(−ay)dy is finite. The remaining part has |x| ≤ 1/2 and √3/2 ≤ y ≤ Y, so is compact inside the upper half-plane; continuity bounds the integrand there. Summing over the finitely many pieces proves absolute integrability.
6. The integral of P(u,v) is independent of the chosen measurable fundamental domain with almost-everywhere unique representatives for the effective action. To see this, partition one domain by its intersections with the translates of the other, indexing by Δ/{±I}. Translate each piece back. Away from the null exceptional boundaries, the resulting pieces partition the other domain. Both P(u,v) and μ are Δ-invariant by step 2. Countable additivity first identifies the absolute integrals, proving integrability on the second domain, and then identifies the complex integrals.
7. Define B_Δ(u,v) = ∫_{F_Δ} P(u,v)dμ. Absolute integrability proves additivity, conjugate-linearity in u, and linearity in v. Conjugating the integrand exchanges u and v. Moreover, B_Δ(u,u) is the integral of the real nonnegative function |u(z)|²(Im z)². If this integral is zero, that function vanishes almost everywhere on F_Δ. Its invariance and countably many translates imply almost-everywhere vanishing on the whole upper half-plane. If u were nonzero at a point, continuity would give an open disk on which the function is bounded below by a positive number. Such a disk has positive μ-measure because y⁻² is a strictly positive density. This is a contradiction. Hence B_Δ(u,u) = 0 implies u = 0. In particular, B_Γ supplies exactly the conjugate symmetry, nonnegative real diagonal, additivity, conjugate scalar law, and definiteness required by InnerProductSpace.Core ℂ V. Fix this B once and for all.
8. We will use rational slash translates on intersection subgroups. Let A ∈ GL₂(ℚ) have positive determinant, and suppose H_A = Δ ∩ A⁻¹ΔA has finite index. For f ∈ S₂(Δ), the function f|₂A is H_A-invariant, since AhA⁻¹ ∈ Δ for h ∈ H_A, and it is holomorphic by the slash formula. At a rational cusp σ∞ choose ρ ∈ SL₂(ℤ) with ρ∞ = Aσ∞. Then ρ⁻¹Aσ = ((a,b),(0,d)) is rational upper triangular with a/d > 0. Slash composition gives ((f|₂A)|₂σ)(z) = (a/d)(f|₂ρ)((a/d)z+b/d), which tends to zero as Im z tends to infinity. Step 1 identifies all cusps of H_A as rational, so f|₂A is a cusp form on H_A. Restricting a cusp form to a finite-index subgroup likewise preserves cuspidality, since the rational cusp sets coincide.
9. Fix a prime p with p ∤ M, and set α = diag(1,p), A_j = ((1,j),(0,p)) for 0 ≤ j < p, and C = diag(p,1). Put H = Γ ∩ α⁻¹Γα and K = Γ ∩ αΓα⁻¹. For γ = ((a,b),(c,d)) ∈ Γ, the matrix αγα⁻¹ is ((a,b/p),(pc,d)); hence γ ∈ H exactly when p divides b. Similarly, γ ∈ K exactly when pM divides c. Both H and K contain Γ(pM), and therefore have finite index, and both contain −I. Also αHα⁻¹ = K.
10. For γ₁,γ₂ ∈ Γ, the upper-right entry of γ₁γ₂⁻¹ is −a₁b₂+b₁a₂. Thus Hγ₁ = Hγ₂ precisely when their nonzero first rows modulo p lie on the same projective line over ℤ/pℤ. These rows are nonzero because the determinants are one. The lines with nonzero first coordinate are represented uniquely by (1,j), 0 ≤ j < p, and hence by t_j = ((1,j),(0,1)) ∈ Γ. Since p ∤ M, choose integers u,v with pu+Mv = 1. The matrices γ_* = ((p,−v),(M,u)) and δ = ((1,−v),(M,pu)) have determinant one and belong to Γ. The first row of γ_* represents the remaining line, since Mv ≡ 1 modulo p implies v ≠ 0 modulo p. Therefore the t_j and γ_* are a complete nonrepeating set of representatives for H\Γ.
11. The correspondence Hγ ↦ Γαγ is a bijection with the left-Γ cosets in ΓαΓ: equality of the latter cosets is equivalent to γ₁γ₂⁻¹ ∈ Γ ∩ α⁻¹Γα. Now αt_j = A_j and αγ_* = δC. Consequently ΓαΓ is the disjoint union of ΓA_j and ΓC. In particular ΓCΓ = ΓαΓ. Since α⁻¹ = p⁻¹C, centrality of scalar matrices gives Γα⁻¹Γ = p⁻¹ΓαΓ.
12. Let D_αf be the slash sum over representatives of the left-Γ cosets in ΓαΓ; it is independent of representative choices because f|₂γ = f for γ ∈ Γ. The frozen definitions Def_ModularForm_HeckeOperator.lean and Def_ModularForm_HeckeOperatorForms.lean identify this sum as T_p f = CuspForm.heckeTLin 2 hp hpM f, by step 11. Representatives for the inverse double coset are p⁻¹A_j and p⁻¹C. Positive scalars act trivially at weight two by step 2, so the corresponding sum D_{α⁻¹} is also exactly T_p. These sums are bundled cusp forms because they equal the defined cusp-form operator.
13. Choose representatives γ_i for H\Γ. Then D_αf = Σ_i f|₂αγ_i, and F_H can be taken to be the union of γ_iF_Γ, up to null boundaries. The functions f|₂α and g are cusp forms on H by step 8, so all the following integrals are absolutely convergent by step 5. Invariance g|₂γ_i = g and covariance give B_Γ(D_αf,g) = Σ_i ∫_{F_Γ} P(f|₂αγ_i,g)dμ = ∫_{F_H}P(f|₂α,g)dμ. Since g = (g|₂α⁻¹)|₂α, the substitution w = αz and step 2 turn the last integral into ∫_{αF_H}P(f,g|₂α⁻¹)dμ.
14. The set αF_H is a fundamental domain for K = αHα⁻¹. Both f and g|₂α⁻¹ are cusp forms on K by step 8, and their Petersson integrand is K-invariant. By step 6 replace αF_H with the union of δ_jF_Γ, where δ_j represent K\Γ. Transporting these pieces back, and using f|₂δ_j = f, yields Σ_j ∫_{F_Γ}P(f,g|₂α⁻¹δ_j)dμ = B_Γ(f,D_{α⁻¹}g). The matrices α⁻¹δ_j represent exactly the inverse double coset, by the same coset correspondence as in step 11 with α replaced by α⁻¹. This proves B_Γ(D_αf,g) = B_Γ(f,D_{α⁻¹}g). No index factors occur because every pairing uses the unnormalized integral.
15. Substituting D_α = D_{α⁻¹} = T_p from step 12 proves B.inner (T_p f) g = B.inner f (T_p g). The construction of B in step 7 did not depend on p, so the same Core works for every good prime. The equality holds for every hp and hpM: these certify the same arithmetic conditions, and the defining underlying function of heckeTLin is independent of those proof witnesses. This establishes the stated existential theorem.

## Key steps

1. Establish finite index, rational cusps, and positive cusp widths.
2. Verify the exact weight-two slash normalization, Petersson covariance, and invariant measure.
3. Construct measurable fundamental domains and prove absolute convergence using cusp decay.
4. Prove domain independence and positive definiteness, producing one InnerProductSpace.Core.
5. Show rational slash translates are cusp forms on the required intersection subgroups.
6. Compute the good-prime double coset using projective first rows and Bézout matrices.
7. Identify the inverse double coset by a positive central scalar.
8. Unfold the two trace sums to prove adjointness without index factors.
9. Identify both trace sums with the exact bundled Hecke operator for every good prime.

## Reference use

### local-project

Queries:
- `rg -n 'heckeTLin|InnerProductSpace.Core|iSup_iInf_eq_top_of_commute|sturm_bound_levelOne_nat' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb`
- `grep -RnE 'finiteDimensional|FiniteDimensional|InnerProductSpace.Core|heckeTLin.*commut|heckeTLin.*[Ss]ymmet'`
- `grep -nE 'Gamma0|FiniteIndex|Normal'`
- `grep -nE 'iSup_iInf_eq_top_of_commute|sturm_bound_levelOne_nat|hasSum_qExpansion|qExpansion_coeff_unique|instFiniteIndexGamma0|petersson_slash|structure InnerProductSpace.Core|eq_one_or_neg_one_of_mem_fdo_mem_fd'`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `#print axioms CuspForm.heckeTLin`
- `#print axioms ModularForm.heckeT_apply`
- `#print axioms CongruenceSubgroup.instFiniteIndexGamma0`
- `#print axioms UpperHalfPlane.hasSum_qExpansion`
- `#print axioms LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`
- `#print axioms ModularForm.sturm_bound_levelOne_nat`
- `#print axioms UpperHalfPlane.petersson_slash`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperator.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean`
- `/tmp/fermat_p01_decomposition_a90tkggj/CheckDependencyTypes.lean`
- `/tmp/fermat_p01_decomposition_a90tkggj/CheckDependencyTypes.log`
- `/tmp/fermat_p01_decomposition_a90tkggj/CheckLibrary.log`
- `/tmp/fermat_p01_decomposition_a90tkggj/Submission.log`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The installed mathlib has that revision and clean status; the compiled project dependency sources match the snapshot byte-for-byte. ripgrep is unavailable, so the attempted rg search was followed by grep and Python file inspection. The sources establish the exact Hecke normalization, finite index, Fourier expansion and uniqueness, level-one Sturm bound, Petersson covariance, invariant measure, InnerProductSpace.Core, and the arbitrary-family simultaneous-eigenspace theorem. No suitable Gamma0 finite-dimensionality or bundled Hecke symmetry/commutation theorem was found in the searched Definitions and mathlib modular-form directories. All seven audited declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. The three proposed types elaborate against the unchanged contract imports; an anonymous rfl check confirms that the inner-product instance induced from B has inner product B.inner. However, literal import Submission validation is blocked: unchanged Submission.lean fails at its attribute commands with unknown constants FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions and FreyPackage.ModMCarrier.coe_rescaleLin_apply. No project source was changed.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/752

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
