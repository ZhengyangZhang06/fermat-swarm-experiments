<!-- theorem-id: fermat-p02/root.scalarization_modular-a1.translation_bound-a1 -->

## Theorem `Submission.p02_es_177ebb5a_sm_translation_bound`

Let N,n∈ℕ with N≠0, let u:ℍ→ℂ be continuous, and let G:ℍ→BinaryForm ℂ n satisfy IsEichlerIntegral n u G. Write T=(1 1;0 1)∈SL₂(ℤ), and assume G(T^N z)=binaryFormRepSL ℂ n (T^N)(G(z)) for every z∈ℍ. Suppose there exist real a,C,Y with a>0 and C≥0 such that |u(z)|≤C exp(−a Im z) whenever Im z≥Y. Then z↦G(z)(1,−z) is bounded at imaginary infinity, uniformly over all real parts.

Node: `root.scalarization_modular-a1.translation_bound-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/28

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/104, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/105, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/107, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/109

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_sm_translation_bound`

```lean
∀ (N : ℕ) [NeZero N] (n : ℕ) (u : UpperHalfPlane → ℂ) (G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), Continuous u → HeckeEis.IsEichlerIntegral n u G → (∀ τ : UpperHalfPlane, G ((ModularGroup.T ^ N) • τ) = ((HeckeEis.binaryFormRepSL ℂ n) (ModularGroup.T ^ N)) (G τ)) → (∃ (a C Y : ℝ), 0 < a ∧ 0 ≤ C ∧ ∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖u τ‖ ≤ C * Real.exp (-a * τ.im)) → UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (G τ).val)
```

### Frozen project context

`Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean` at `1f74c284b125d4c45f527f2d621597fcf1e103a9` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HeckeEis_eichlerShimuraMap_injective.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_injective (N : ℕ) [NeZero N] (n : ℕ) :
    Function.Injective
      (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f) := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the witnesses a,C,Y, and identify the positive natural number N with its positive real value. Write each R∈BinaryForm ℂ n uniquely as Σ_{r=0}^n R_rX^rY^(n−r), and set ‖R‖c=max_{0≤r≤n}|R_r|. These coordinates identify the space with ℂ^(n+1), so this norm is complete. On the open upper half-plane the derivative predicate gives G′(z)=u(z)(zX+Y)^n coefficientwise. Since u is continuous, these coefficient derivatives are continuous. The fundamental theorem of calculus therefore applies to their restrictions to horizontal and vertical segments.
2. Put y₀=max(1,Y). For 0≤x≤N and t≥y₀, one has |x+it|≤N+t≤(N+1)(1+t). The coefficient of X^rY^(n−r) in (zX+Y)^n is binom(n,r)z^r, with binom(n,r)≤2^n. Consequently, for D=C·2^n·(N+1)^n≥0, one has ‖G′(x+it)‖c≤D(1+t)^n exp(−at) throughout this strip.
3. The nonnegative integral J=∫₀^∞(1+s)^n exp(−as) ds is finite. Indeed, (1+s)^n≤2^n(1+s^n) for s≥0. The exponential series gives s^n≤n!(2/a)^n exp(as/2). Therefore the integrand is bounded by 2^n(1+n!(2/a)^n)exp(−as/2), whose integral is 2^(n+1)(1+n!(2/a)^n)/a. This also proves finiteness when n=0.
4. For fixed x∈[0,N] and t≥y≥y₀, integrate along the vertical segment. Its derivative is iG′(x+is), which has the same coefficient norm as G′(x+is). The fundamental theorem and the triangle inequality give ‖G(x+it)−G(x+iy)‖c≤D∫_y^t(1+s)^n exp(−as) ds. Substituting s=y+v and using 1+y+v≤(1+y)(1+v) yields the bound D J (1+y)^n exp(−ay).
5. For every nonnegative integer m, (1+y)^m exp(−ay) tends to zero as y→∞. For y≥1, it is at most 2^m y^m exp(−ay), and the exponential-series inequality exp(ay)≥(ay)^(m+1)/(m+1)! bounds this by 2^m(m+1)!/(a^(m+1)y). Applying this with m=n to step 4 proves that G(x+iy) is Cauchy as y→∞. Completeness gives a limit A_x, and passage to the limit t→∞ in step 4 gives ‖G(x+iy)−A_x‖c≤D J (1+y)^n exp(−ay).
6. Horizontal integration at height y gives ‖G(x+iy)−G(iy)‖c≤xD(1+y)^n exp(−ay) for every x∈[0,N]. The right side tends to zero by step 5. Thus A_x=A_0 for every x in the strip, including x=N. Write their common value as A. The estimate in step 5 is consequently uniform over the whole strip.
7. The matrix T^N acts by z↦z+N. Translation equivariance gives G(N+iy)=ρ(T^N)G(iy), where ρ=binaryFormRepSL ℂ n. Linear substitution is continuous in the finite coefficient coordinates, so taking the limits at x=N and x=0 gives A=ρ(T^N)A. The substitution for T^N is (X,Y)↦(X,NX+Y). Applying X↦1 and Y↦t gives the polynomial identity r(t+N)=r(t), where r(t)=A(1,t).
8. If r had positive degree d and leading coefficient b≠0, then the coefficient of t^(d−1) in r(t+N)−r(t) would be dbN. Lower-degree terms contribute nothing to that coefficient, and dbN≠0 because ℂ has characteristic zero and N>0. This contradicts the polynomial identity. Thus r is constant, say α, including the possibility r=0. The homogeneous expansion then forces A=αX^n, so A(1,−z)=α for all z. This includes n=0.
9. For every homogeneous R, its expansion gives |R(1,−z)|≤(n+1)max(1,|z|)^n‖R‖c. On 0≤x≤N and y≥1, max(1,|x+iy|)≤(N+2)(1+y). Apply these inequalities to R=G(x+iy)−A and use step 6. With K=(n+1)(N+2)^n D J≥0, this gives |G(x+iy)(1,−x−iy)−α|≤K(1+y)^(2n)exp(−ay), uniformly for x∈[0,N] and y≥y₀. Step 5 with m=2n shows that this bound tends to zero. Hence there exists Y₁≥y₀ for which the scalarization has absolute value at most |α|+1 throughout the strip whenever y≥Y₁.
10. Let q(z)=G(z)(1,−z). Translation equivariance and the substitution formula give q(z+N)=(ρ(T^N)G(z))(1,−z−N)=G(z)(1,N−z−N)=q(z). Iterating this equality proves invariance under positive integer translates; applying it at z−N proves invariance under negative translates as well.
11. For any z=x+iy∈ℍ with y≥Y₁, put m=floor(x/N). Since N>0, the real part x−mN belongs to [0,N). Periodicity gives q(z)=q(z−mN), while the imaginary part remains y. Step 9 therefore gives |q(z)|≤|α|+1 for every real x. The criterion UpperHalfPlane.isBoundedAtImInfty_iff in Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean identifies this uniform eventual bound with the exact conclusion.

## Key steps

1. Use finite homogeneous coefficient coordinates and continuous coefficient derivatives.
2. Bound the derivative by a polynomial times an exponential on a translation strip.
3. Prove integrability of the tail and obtain uniform vertical convergence.
4. Use horizontal integration to identify the limits on all rays in the strip.
5. Take limits in translation equivariance.
6. Show that a translation-invariant homogeneous limit is αX^n.
7. Control evaluation of the decaying error and obtain a uniform strip bound.
8. Use scalar periodicity and integer translations to cover every real part.

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


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/613

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
