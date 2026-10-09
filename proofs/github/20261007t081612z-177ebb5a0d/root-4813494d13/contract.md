<!-- theorem-id: fermat-p02/root -->

## Theorem `HeckeEis.eichlerShimuraMap_injective`

Prove `HeckeEis.eichlerShimuraMap_injective` for `fermat-p02` using the exact frozen contract in `Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean`. Write the Lean solution in Submission.lean. Use the issue/PR workflow: complete and independently review the natural-language proof, publish every new named helper as an issue, and require the controller comparator and independent review before a solution PR is merged and its issue closed. Workers independently poll issues; do not dispatch or notify other workers. No web search. Do not import the original upstream solution of this target. Pinned unchanged libraries may be reused with exact provenance and axiom checks.

Node: `root`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: None (root)

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/26, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/27, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/28, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/29, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/30

## Lean problem

Declaration: `HeckeEis.eichlerShimuraMap_injective`

```lean
∀ (N : ℕ) [NeZero N] (n : ℕ), Function.Injective (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f)
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

# Final proof of `HeckeEis.eichlerShimuraMap_injective`

## Statement and assumptions

For every natural number `N` with `[NeZero N]` and every natural number `n`, the function

```lean
fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦
  HeckeEis.eichlerShimuraMap n N f
```

is injective. There are no additional hypotheses. In particular, `n = 0` is included. Let Γ be `CongruenceSubgroup.Gamma0 N`, let V be `HeckeEis.BinaryForm ℂ n`, and let ρ be `(HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype`. Thus V consists of homogeneous degree-n binary polynomials, and ρ is the prescribed polynomial representation restricted to Γ. Write L(z) = (zX + Y)^n. The predicate `IsEichlerIntegral n h E` means, for every polynomial coefficient index d and every τ in the upper half-plane, that the derivative of the d-th coefficient of `E (UpperHalfPlane.ofComplex z)` at z = τ is h(τ) times the d-th coefficient of L(τ). Every derivative statement below uses this exact predicate.

## Accepted dependencies actually used

All five declarations below are existing, separately tracked accepted dependencies in `Submission.lean`. They are not new assumptions or newly introduced helper theorems. Their implementations and their own accepted prerequisites remain in the integrated file.

1. `Submission.p02_es_177ebb5a_primitive_exists`: for every N, `[NeZero N]`, n, and f in the cusp-form space in the statement, there is F : ℍ → V with `IsEichlerIntegral n (fun τ => f τ) F` and `IsEquivariantPrimitiveWith ρ F`. The latter says that F(γτ) − ρ(γ)F(τ) is independent of τ for every γ in Γ. Its accepted proof constructs scalar holomorphic primitives, packages the homogeneous coefficients, and uses the modular transformation law to show that each defect has derivative zero on the connected upper half-plane.
2. `Submission.p02_es_177ebb5a_primitive_parabolic`: for the same N, n, f, any F with that Eichler-integral predicate, and any proof hF of the constant-defect property, the cocycle `hF.cocycle` is parabolic. Its accepted proof uses the cusp decay of slash transforms, limits of primitives, and the integral normal form for matrices with trace squared equal to four. The limiting polynomial expresses each tested defect as an element of the range of ρ(γ) − 1, including the central and trace −2 cases.
3. `Submission.p02_es_177ebb5a_equivariant_primitive_vanishes`: for the same N, n and cusp form h, if E satisfies `IsEichlerIntegral n (fun τ => h τ) E` and E(γτ) = ρ(γ)E(τ) for every γ in Γ and τ in ℍ, then h = 0. The root invokes this declaration directly. Its proof uses the following two accepted dependencies, so both are also actual transitive dependencies of the final argument.
4. `Submission.p02_es_177ebb5a_scalarization_modular`: under exactly the hypotheses of item 3, there is a modular form p of weight −n on Γ such that p(τ) = E(τ)(1,−τ). In particular this conclusion includes boundedness at every cusp, not just holomorphy and the transformation law. The accepted implementation obtains holomorphy coefficientwise, the slash identity by the binary polynomial action, and the cusp bounds from exponentially decaying derivatives and translation-invariant limiting polynomials.
5. `Submission.p02_es_177ebb5a_scalarization_derivative`: for every n, h : ℍ → ℂ, and E : ℍ → V, if `fun z => h (UpperHalfPlane.ofComplex z)` is complex differentiable on `{z | 0 < z.im}` and `IsEichlerIntegral n h E`, then at every τ in ℍ the (n+1)-st derivative of `fun z => E (UpperHalfPlane.ofComplex z)(1,−z)` is `((-1 : ℂ)^n * (Nat.factorial n : ℂ)) * h τ`. Its accepted implementation differentiates the moving evaluation, proves the finite partial-derivative recurrence, and iterates that recurrence on the open upper half-plane.

For clarity, the vanishing argument in item 3 is complete as follows. Item 4 supplies p. Since N is nonzero, Γ₀(N) has finite index and its prescribed real matrix image is arithmetic. The pinned theorems `ModularForm.isZero_of_neg_weight` and `ModularForm.eq_const_of_weight_zero` therefore apply. If n is positive, p has negative weight and is zero; if n is zero, p is constant. In either case choose c with p(τ) = c for all τ. The scalarization P(z) equals c on the open set of positive imaginary part. Locality of iterated derivatives (`Set.EqOn.iteratedDeriv_of_isOpen`) makes its (n+1)-st derivative zero at every τ in ℍ. Holomorphy of the cusp form supplies item 5's differentiability assumption through `UpperHalfPlane.mdifferentiable_iff`. Item 5 then gives `((-1)^n n!) h(τ) = 0`. Both factors of `(-1)^n n!` are nonzero in ℂ, including when n = 0. Consequently h(τ) = 0 for every τ, and `CuspForm.ext` gives h = 0. There is no unproved geometric or cusp-boundedness obligation in this invocation: those are the exact conclusions of the preserved accepted declarations.

## Numbered proof of the root

1. Fix N, `[NeZero N]`, and n. Let f and g be cusp forms of weight n+2 on Γ and assume that their values under the frozen `eichlerShimuraMap n N` are equal. We prove f = g. The proof uses classical choice, consistently with the definition of this map.

2. Apply `primitive_exists` to f and g. This gives preliminary primitives F₁ and G₁ and their constant-defect properties. Apply `primitive_parabolic` to each preliminary primitive and its supplied proof of constant defects. Thus the existential condition in the frozen definition of the map holds for both cusp forms.

3. Apply the pinned project theorem `HeckeEis.eichlerShimuraMap_def` to each of these witnesses. It supplies primitives F and G actually representing the chosen map values, their Eichler-integral properties, proofs hFeq and hGeq of constant defects, their parabolicity proofs, and equalities identifying the two map values with their cocycle classes. It is not necessary to identify F with F₁ or G with G₁. In particular no independence-of-arbitrary-choices assertion is assumed.

4. Let cf and cg be the elements of `coeffParabolicCocycles ρ` formed from `hFeq.cocycle` and `hGeq.cocycle`. Membership as cocycles follows from the pinned `IsEquivariantPrimitiveWith.cocycle_mem_coeffCocycles`; their parabolicity was supplied in step 3. In Lean, `change` first writes the map-equality hypothesis explicitly with the functions `fun τ => f τ` and `fun τ => g τ`; this is a definitional change only. Rewriting the hypothesis with the two equalities from step 3 gives `coeffH1parMk ρ cf = coeffH1parMk ρ cg`. This quotient map is linear, so the class of cf − cg is zero, by preservation of subtraction and cancellation.

5. By `HeckeEis.coeffH1parMk_eq_zero_iff`, the underlying function cf − cg belongs to `coeffCoboundaries ρ`. By `HeckeEis.mem_coeffCoboundaries_iff`, there is v in V such that the function γ ↦ ρ(γ)v − v equals that underlying function. Evaluating this function equality and reversing its orientation yields

   `hFeq.cocycle γ - hGeq.cocycle γ = ρ γ v - v`

   for every γ in Γ. This fixes the sign of the correcting constant in the next step.

6. Put E(τ) = F(τ) − G(τ) + v, and put h = f − g, using the existing subtraction in the bundled cusp-form space. For each coefficient index d and τ, subtract the derivative supplied by G from the derivative supplied by F and then add the constant coefficient of v. The derivative is

   `f τ * coeff d (L τ) - g τ * coeff d (L τ)`

   which equals `(f - g) τ * coeff d (L τ)` by distributivity and pointwise subtraction of cusp forms. Coefficients preserve addition and subtraction. The pinned derivative rules `HasDerivAt.fun_sub` and `HasDerivAt.add_const` thus prove the exact predicate `IsEichlerIntegral n (fun τ => (f - g) τ) E` for every coefficient, without a finite-support restriction.

7. Fix γ in Γ and τ in ℍ. The pinned `IsEquivariantPrimitiveWith.apply_smul` identities say

   F(γτ) = cf(γ) + ρ(γ)F(τ), and G(γτ) = cg(γ) + ρ(γ)G(τ).

   Consequently, using step 5 and linearity of ρ(γ),

   E(γτ) = cf(γ) − cg(γ) + v + ρ(γ)F(τ) − ρ(γ)G(τ)
   = ρ(γ)v − v + v + ρ(γ)F(τ) − ρ(γ)G(τ)
   = ρ(γ)(F(τ) − G(τ) + v) = ρ(γ)E(τ).

   These are equalities in the additive group V; the Lean proof rearranges them with `abel` after rewriting the linear maps. Hence E is exactly Γ-equivariant.

8. Apply `Submission.p02_es_177ebb5a_equivariant_primitive_vanishes` with cusp form f − g and primitive E. Step 6 supplies its derivative hypothesis and step 7 supplies its equivariance hypothesis, with the same N, n, and prescribed representation. It follows that f − g = 0. The additive-group equivalence `sub_eq_zero` gives f = g. This proves the frozen injectivity statement for all the required N and n.

## Provenance and preservation

The authoritative mathematical history is `nodes/root/natural-proof-v5.md` under the run directory below, with the separately reviewed child proof bundles and their accepted DAG declarations. The older `plan-draft-v1.md` and its speculative interfaces remain historical; no new decomposition or certification interfaces are used. The final Lean argument follows steps 8–9 and 14 of the accepted proof, with the analytic steps discharged by the actual accepted dependencies listed above. The inherited speculative root text was not treated as proof acceptance: it was moved after its real dependencies, its map-equality hypothesis was normalized for rewriting, and it is subject to the fresh build and exact comparator. Repeated overlay copies of accepted child declarations and stray tactics following an already completed proof were removed, retaining every accepted global name and its original signature. The scalarization proof was checked against its accepted candidate `537923ce7bff4b48b3fa122200f9ecb8853d8e9d`. No new named helper was added.

Run directory:
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d`.

## Reference use

`reference_use` contains exactly one source entry:

```json
[{"source":"local-project","snapshot":"/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b","project_commit":"1f74c284b125d4c45f527f2d621597fcf1e103a9","mathlib_commit":"db584cd6d46c92f209a44c0f1c829460d327499d"}]
```

All paths in the following paragraph are relative to that exact snapshot. `manifest.json` records the two revisions above. The frozen problem supplies the unchanged root statement. Searching with `rg -n 'eichlerShimuraMap_def|coeffH1parMk_eq_zero_iff|mem_coeffCoboundaries_iff|apply_smul|def IsEichlerIntegral' project/Definitions` located the witness-extraction theorem and coefficientwise derivative predicate in `project/Definitions/Def_HeckeEis_EichlerIntegral.lean` (lines 105 and 123), the constant-defect identity and cocycle membership there (lines 83 and 87), and the two quotient/coboundary equivalences in `project/Definitions/Def_Gamma0CoeffCohomology.lean` (lines 48 and 118). Both full files were inspected. These are pinned pre-existing library results, not accepted child declarations or newly invented helpers. The same representation and coefficient operations are used throughout.

The direct calculus rules are in `mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`: the alias `HasDerivAt.add_const` is at line 110, and `HasDerivAt.sub` at line 356 has the `to_fun` attribute producing the `fun_sub` version used here. These source passages were inspected. The remaining direct steps use the standard linear-map, submodule, polynomial-coefficient, and additive-group identities from the same pinned `Mathlib` import, with explicit arguments supplied to `map_sub` for the quotient linear map. The vanishing dependency's nonpositive-weight results were inspected in `mathlib/Mathlib/NumberTheory/ModularForms/NormTrace.lean`, lines 141 and 164; their arithmetic-subgroup assumptions match Γ₀(N) with N nonzero. The exact query `rg -n 'eichlerShimuraMap|IsEichlerIntegral|scalarization' mathlib/Mathlib` returned no matches. Thus mathlib supplies the stated calculus and modular-form infrastructure, not an upstream proof of the target. No network search or alternate target solution was used. Source provenance alone is not formal acceptance; the configured comparator checks the frozen root and retained child interfaces, pinned clean dependencies, permitted transitive axioms, and kernel replay. Independent publication-proof review remains an outer-controller gate.

## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
