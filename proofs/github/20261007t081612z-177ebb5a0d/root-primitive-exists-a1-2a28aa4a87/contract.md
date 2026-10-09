<!-- theorem-id: fermat-p02/root.primitive_exists-a1 -->

## Theorem `Submission.p02_es_177ebb5a_primitive_exists`

Let N,n be natural numbers with N ≠ 0, Γ = Γ₀(N), V = BinaryForm ℂ n, and ρ the restriction of binaryFormRepSL ℂ n to Γ. For every cusp form f of weight n+2 on the prescribed real matrix image of Γ, there exists F : ℍ → V satisfying IsEichlerIntegral n f F and IsEquivariantPrimitiveWith ρ F. Thus its coefficientwise derivative is f(z)(zX+Y)^n, and for every γ ∈ Γ the expression F(γz)−ρ(γ)F(z) is independent of z.

Node: `root.primitive_exists-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/37, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/38, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/39

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_primitive_exists`

```lean
∀ (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)), ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n), HeckeEis.IsEichlerIntegral n (fun τ => f τ) F ∧ HeckeEis.IsEquivariantPrimitiveWith ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F
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
- Child DAG node: `root.primitive_exists-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put Γ=Γ₀(N), V=BinaryForm ℂ n, L(z)=(zX+Y)^n, and let ρ denote the binary-form representation restricted to Γ. The cusp-form hypothesis implies that f is holomorphic. Every element of V has a unique expansion Σ_{r=0}^n a_r X^rY^{n-r}, because its nonzero monomials have total degree n.
2. Every holomorphic scalar function a on ℍ has a primitive. To prove this using the pinned disk-primitive theorem, let φ(w)=i(1+w)/(1−w) on |w|<1 and ψ(z)=(z−i)/(z+i) on ℍ. The identities Im φ(w)=(1−|w|²)/|1−w|² and |z+i|²−|z−i|²=4 Im z show that these maps take their respective domains into ℍ and the unit disk. Their denominators do not vanish there, and direct substitution proves that they are inverse holomorphic maps. The function b(w)=a(φ(w))φ′(w) is holomorphic on the unit disk. Apply DifferentiableOn.isExactOn_ball from Mathlib/Analysis/Complex/HasPrimitives.lean to obtain B with B′=b on that disk. Then A=B∘ψ satisfies A′(z)=a(φ(ψ(z)))φ′(ψ(z))ψ′(z)=a(z), since differentiating φ∘ψ=id gives φ′(ψ(z))ψ′(z)=1.
3. Apply step 2 to each a_r(z)=binom(n,r)f(z)z^r, for 0≤r≤n, and choose primitives A_r. Define F(z)=Σ_{r=0}^n A_r(z)X^rY^{n-r}. This polynomial is homogeneous of degree n. The binomial theorem and coefficientwise differentiation give F′(z)=f(z)L(z). For coefficient indices of total degree different from n, both sides have coefficient zero; every index of total degree n is one of the displayed monomials. Thus the derivative assertion holds for every index quantified by IsEichlerIntegral. Around each τ∈ℍ, positivity of imaginary part persists, so composing F with ofComplex gives the same local coefficient functions. Consequently this is precisely the frozen IsEichlerIntegral predicate.
4. Fix γ=(a b; c d)∈Γ and write j=cz+d. This denominator is nonzero on ℍ: when c≠0 its possible zero is real, while c=0 forces d≠0. The determinant-one identity gives (γz)′=j⁻². Substitution in the binary form gives ρ(γ)L(z)=j^nL(γz), also recorded as HeckeEis.binaryFormRepSL_linePow. The cusp form's slash-invariance, with determinant one, gives f(γz)=j^(n+2)f(z).
5. Differentiate D_γ(z)=F(γz)−ρ(γ)F(z) coefficientwise. The representation is a fixed linear substitution, hence each output coefficient is a finite linear combination of input coefficients. The derivative of the first term is f(γz)L(γz)j⁻²=f(z)ρ(γ)L(z), which equals the derivative of the second term. Therefore every coefficient of D_γ has derivative zero.
6. Given z,w∈ℍ, their straight segment lies in ℍ. The restriction of each coefficient of D_γ to this segment has real derivative zero by the chain rule. Applying the real mean-value theorem to its real and imaginary parts makes its endpoint values equal. Polynomial coefficient uniqueness gives D_γ(z)=D_γ(w). Choosing w=i and c=D_γ(i) proves the existential constant required by IsEquivariantPrimitiveWith for every γ. Together with step 3 this proves the claimed pair of properties.

## Key steps

1. Transfer disk primitive existence to the upper half-plane using the explicit Cayley biholomorphism.
2. Integrate the finitely many coefficients of f(z)(zX+Y)^n.
3. Check every coefficient index and the local ofComplex convention.
4. Differentiate equivariance defects using modularity and binaryFormRepSL_linePow.
5. Use convexity and zero derivative to make each defect constant.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/640

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
