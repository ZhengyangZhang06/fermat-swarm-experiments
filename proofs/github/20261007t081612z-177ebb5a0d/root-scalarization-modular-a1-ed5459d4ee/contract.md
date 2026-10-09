<!-- theorem-id: fermat-p02/root.scalarization_modular-a1 -->

## Theorem `Submission.p02_es_177ebb5a_scalarization_modular`

Let N,n∈ℕ with N≠0, Γ=Γ₀(N), V=BinaryForm ℂ n, and ρ the restricted binary-form representation. Let f be a weight n+2 cusp form and E : ℍ → V satisfy IsEichlerIntegral n f E and E(γz)=ρ(γ)E(z) for every γ∈Γ and z∈ℍ. Then there exists a bundled modular form p of weight −n on the prescribed real matrix image of Γ such that p(z)=E(z)(1,−z) for every z. In particular, the assertion includes holomorphy, slash invariance, and the full bounded-at-cusps condition.

Node: `root.scalarization_modular-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/45, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/46, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/47, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/48, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/49

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_scalarization_modular`

```lean
∀ (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n (fun τ => f τ) E → (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane), E ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) = ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) γ (E τ)) → ∃ p : ModularForm (CongruenceSubgroup.Gamma0 N) (-(n : ℤ)), ∀ τ : UpperHalfPlane, p τ = MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (E τ).val
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

- Parent DAG node: `root`
- Child DAG node: `root.scalarization_modular-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put V=BinaryForm ℂ n and let ρ denote its full SL₂(ℤ) representation. Define p(z)=E(z)(1,−z). The predicate IsEichlerIntegral supplies a complex derivative for every coefficient of E at every point of ℍ. Since ofComplex agrees locally with the upper-half-plane coordinate, these coefficient functions are holomorphic. The finite homogeneous expansion of E expresses p as a finite sum of holomorphic functions times powers of −z. Hence p is holomorphic, with the manifold interpretation justified by UpperHalfPlane.mdifferentiable_iff in Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean.
2. For γ=(a b;c d)∈Γ, let j=cz+d. It is nonzero on ℍ. Determinant one gives a−cγz=1/j and b−dγz=−z/j. Equivariance, the defining substitution for ρ, and degree-n homogeneity imply p(γz)=E(z)(a−cγz,b−dγz)=j^(−n)p(z). This proves the required slash invariance for every element in the real matrix image of Γ, since each such element has a representative γ∈Γ.
3. Fix σ∈SL₂(ℤ), set u=f|_{n+2}σ, and define G(z)=ρ(σ⁻¹)E(σz). The identity ρ(σ)(zX+Y)^n=j(σ,z)^n((σz)X+Y)^n and (σz)′=j(σ,z)⁻² give G′(z)=u(z)(zX+Y)^n coefficientwise. Repeating the evaluation calculation in step 2 with E(σz)=ρ(σ)G(z) gives (p|_{−n}σ)(z)=G(z)(1,−z).
4. The principal congruence subgroup Γ(N), the kernel of reduction modulo N, is normal and contained in Γ. It contains T^N, where T=(1 1;0 1). Thus σT^Nσ⁻¹∈Γ, so u has period N and σ∞ is a cusp, witnessed by this noncentral parabolic matrix. The cusp-form condition says u tends uniformly to zero as imaginary height tends to infinity. It is holomorphic because its slash denominator is nonzero. For q=exp(2πiz/N), periodicity descends u to a holomorphic U on the punctured unit disk. Uniform vanishing extends U continuously by U(0)=0; the removable-singularity theorem makes the extension holomorphic. Its power series gives U(q)=qV(q), with V bounded near zero. Therefore |u(x+iy)|≤C exp(−ay) for all real x and sufficiently large y, where a=2π/N>0. These are also the exact hypotheses of UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty in Mathlib/NumberTheory/ModularForms/QExpansion.lean.
5. Equip V with the maximum norm of coefficients in X^rY^{n-r}. For |x|≤B and t≥1, the coefficients of (x+it)X+Y raised to degree n are bounded by a constant times (1+t)^n. Consequently ‖G′(x+it)‖≤C_B(1+t)^n exp(−at). Vertical integration bounds tails by C_B J(1+y)^n exp(−ay), where J=∫₀^∞(1+s)^n exp(−as) ds<∞. The inequality follows from 1+y+s≤(1+y)(1+s); finiteness follows by expanding the polynomial and using ∫₀^∞s^r exp(−as) ds=r!/a^(r+1), proved by integration by parts. Boundary terms vanish since exp(as)≥(as)^(r+1)/(r+1)!. Completeness of the finite coefficient space gives a limit on each vertical ray. Horizontal integration bounds the difference between rays at height y by |x−x′|C_B(1+y)^n exp(−ay), which tends to zero. Thus the limits agree in one A∈V, and ‖G(x+iy)−A‖≤K_B(1+y)^n exp(−ay) uniformly for |x|≤B and sufficiently large y.
6. Exact equivariance under σT^Nσ⁻¹ gives G(z+N)=ρ(T^N)G(z). Taking the common ray limits at real parts 0 and N gives A=ρ(T^N)A, since linear substitution is continuous on V. Write r(t)=A(1,t). The substitution ρ(T^N) sends (X,Y) to (X,NX+Y), so r(t+N)=r(t). If r had positive degree d with leading coefficient b≠0, the coefficient of t^(d−1) in r(t+N)−r(t) would be dbN≠0, a contradiction. Thus r is constant. The unique homogeneous expansion then implies A=αX^n for some α∈ℂ. This includes n=0 and A=0.
7. For any R∈V, its homogeneous expansion gives |R(1,−z)|≤(n+1)max(1,|z|)^n‖R‖. On 0≤x≤N and y≥1, max(1,|x+iy|)≤(N+2)(1+y). Apply this to R=G(x+iy)−A and step 5. Since A(1,−z)=α, one obtains |G(x+iy)(1,−x−iy)−α|≤K(1+y)^(2n)exp(−ay) on that strip for large y. The right side tends to zero: for y≥1 use (1+y)^(2n)≤2^(2n)y^(2n) and exp(ay)≥(ay)^(2n+1)/(2n+1)!. Thus the scalarization is eventually uniformly bounded on the strip.
8. It is N-periodic, because G(z+N)=ρ(T^N)G(z) implies G(z+N)(1,−z−N)=G(z)(1,−z). For every real x, taking m=floor(x/N) gives x−mN∈[0,N). Periodicity, also for negative integer translates, reduces every real part to this strip without changing its imaginary part. Step 7 therefore proves boundedness at imaginary infinity for G(z)(1,−z), hence for p|_{−n}σ by step 3.
9. It remains to check every cusp in the bundled definition. Reduction modulo the positive integer N has finite image, so Γ(N) has finite index, and its inclusion in Γ implies that Γ has finite index. The prescribed real matrix image is therefore arithmetic, as in Subgroup.isArithmetic_iff_finiteIndex. The pinned results Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z and isCusp_SL2Z_iff′ in Mathlib/NumberTheory/ModularForms/Cusps.lean imply that every cusp is σ∞ for some σ∈SL₂(ℤ). For that σ, step 8 gives boundedness of the required slash translate. OnePoint.isBoundedAt_iff in Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean converts boundedness after this single scaling matrix into the full cusp predicate, including all other real scaling matrices. Its hypothesis is precisely that the selected matrix sends infinity to this cusp, which is how σ was chosen.
10. Package the scalar function from step 1 with its holomorphy, the slash invariance from step 2, and the cusp boundedness from step 9 into ModularForm Γ (−n). Its underlying function is exactly the stated evaluation of E, proving the existential conclusion.

## Key steps

1. Use coefficientwise differentiability to obtain holomorphic scalarization.
2. Calculate its weight −n transformation law by determinant one and homogeneity.
3. Express every slash translate through the corresponding transformed primitive.
4. Prove exponential cusp decay and a uniform polynomial-times-exponential primitive tail.
5. Use translation equivariance to force the limiting polynomial to be αX^n.
6. Bound evaluation on one strip and extend the bound by periodicity.
7. Apply arithmetic cusp classification and the full scaling-matrix criterion, then bundle the modular form.

## Reference use

### local-project

Queries:
- `rg --files --hidden -g AGENTS.md -g Submission.lean -g lakefile.lean -g lake-manifest.json -g lean-toolchain -g '*dag*' -g '*decomposition*' -g '*state*' -g '!**/.git/**' -g '!**/node_modules/**' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d .`
- `IsEichlerIntegral|IsEquivariantPrimitiveWith|coeffH1parMk_eq_zero_iff|p02_es_177ebb5a_`
- `p02_es_177ebb5a_|scalarization`
- `isZero_of_neg_weight|eq_const_of_weight_zero|exp_decay_atImInfty|isBoundedAt_iff|isCusp_SL2Z|isArithmetic_iff_finiteIndex`
- `Gamma0|FiniteIndex`
- `iteratedDeriv|def `
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_es_177ebb5a_typecheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/RemovableSingularity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/NormTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. rg was unavailable, so searches used grep. The defining files confirm the coefficientwise derivative predicate, constant-defect cocycle, existence branch, trace-squared parabolic test, and quotient by coboundaries. HasPrimitives supplies disk primitives; QExpansion supplies exponential decay; BoundedAtCusp supplies the full scaling-matrix criterion; NormTrace supplies negative-weight vanishing and weight-zero constancy. No scalarization helper matched in the searched P2M directory, and no proposed identifier matched the searched declarations or current DAG, which contains only the root. The six transitive project definition files matched the snapshot; all installed dependencies matched their pinned revisions with clean tracked sources. All five proposed types elaborated under Lean 4.33.1 with only import Submission. Their elaborated modular-form groups use the prescribed mapGL image of Gamma0. Axiom checks of the reused primitive, representation, quotient, decay, cusp, and weight theorems returned only propext, Classical.choice, and Quot.sound. These are interface and library checks, not comparator acceptance of any new proof.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
