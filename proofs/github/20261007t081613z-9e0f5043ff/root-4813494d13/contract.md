<!-- theorem-id: fermat-p06/root -->

## Theorem `AlgebraicCurve.hasPrincipalDivisors_of_transcendental`

Prove `AlgebraicCurve.hasPrincipalDivisors_of_transcendental` for `fermat-p06` using the exact frozen contract in `Fermat/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean`. Write the Lean solution in Submission.lean. Use the issue/PR workflow: complete and independently review the natural-language proof, publish every new named helper as an issue, and require the controller comparator and independent review before a solution PR is merged and its issue closed. Workers independently poll issues; do not dispatch or notify other workers. No web search. Do not import the original upstream solution of this target. Pinned unchanged libraries may be reused with exact provenance and axiom checks.

Node: `root`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: None (root)

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/34, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/35, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/36

## Lean problem

Declaration: `AlgebraicCurve.hasPrincipalDivisors_of_transcendental`

```lean
∀ (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F], HasPrincipalDivisors K F
```

### Frozen project context

`Fermat/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean` at `956e8c600d8b95b46948ae5e37b13930b5f3d06b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Final proof of AlgebraicCurve.hasPrincipalDivisors_of_transcendental

## Statement and assumptions

Let `K` be a field of characteristic zero, `F` a field with a `K`-algebra structure,
and `x : F` transcendental over `K`. Assume that `F` is finite-dimensional over
`E = IntermediateField.adjoin K ({x} : Set F)`. We prove exactly
`AlgebraicCurve.HasPrincipalDivisors K F`: every nonzero `f : F` has a finitely
supported integer divisor `D` whose coefficient at every place `w` is `w.ord f`
and whose degree is zero. A divisor is a finitely supported function on the
project's places, and its degree is the sum of its coefficients multiplied by
the corresponding residue degrees over `K`.

## Accepted dependencies used directly

These are existing, independently tracked child declarations, not new helpers.
All fields and algebras in the following statements have their given compatible
structures.

1. `Submission.p06_9e0f5043ff_rational_adjoin_principal`: for fields `K, F`, a
   `K`-algebra `F`, and any transcendental `x : F`, the intermediate field `K(x)`
   has principal divisors over `K`. No characteristic or finite-extension
   hypothesis is needed for this child.
2. `Submission.p06_9e0f5043ff_finite_order_support_ascent`: for fields `K, E, L`
   with `K`-algebras `E, L`, an `E`-algebra `L`, a compatible scalar tower, and
   finite-dimensional separable extension `L/E`, if every nonzero `a : E` has
   finite order support on `Place K E`, then every nonzero `f : L` has finite
   order support on `Place K L`.
3. `Submission.p06_9e0f5043ff_local_norm_order`: under those same tower,
   finite-dimensionality, and separability assumptions, for every downstairs
   place `v` and nonzero `f : L`,
   `v.ord (Algebra.norm E f) = ∑ w ∈ v.fiberOver L, (w.inertiaDeg E : ℤ) * w.ord f`.
   The fiber is the finite set of places restricting to `v`; inertia degree
   means the residue-field degree over the restricted place.

## Numbered proof matching the Lean argument

1. Set `E = K(x)` with its canonical field and algebra structures. The
   intermediate-field structures supply the compatible tower `K → E → F`.
   The map `K → E` is injective because it is a field homomorphism, so `E` has
   characteristic zero. The assumed finite-dimensionality makes `F/E`
   integral, and an integral extension of a characteristic-zero field is
   separable. This supplies precisely the instances needed by children 2 and 3.

2. Apply child 1 to `K, F, x` and the given transcendence proof to obtain
   `HasPrincipalDivisors K E`. For each nonzero `a : E`, choose the divisor
   `A` supplied by this property. Since `A(v) = v.ord a`, every place where
   `v.ord a ≠ 0` belongs to `A.support`. The latter is a finite set, so the
   order support of every nonzero element of `E` is finite. The degree-zero
   part of this particular witness is unnecessary for this step.

3. Fix any nonzero `f : F`. Child 2, with the finite support property from
   step 2, proves finiteness of `{w : Place K F | w.ord f ≠ 0}`. Define `D` by
   `Finsupp.ofSupportFinite (fun w => w.ord f)` and this finiteness proof.
   Thus `D` is a divisor and `D(w) = w.ord f` for every `w`, by the definition
   of `ofSupportFinite`. It remains to prove its degree is zero.

4. Put `g = Algebra.norm E f`. Because `F/E` is finite-dimensional and `f`
   is nonzero, its norm is nonzero. Apply `HasPrincipalDivisors K E` to `g`
   and obtain a divisor `A` with `A(v) = v.ord g` for every downstairs place
   and `degree A = 0`.

5. We show `Divisor.pushforward E D = A` by equality of coefficients.
   At a place `v`, the library's `pushforward_apply` gives the finite sum
   over `D.support` of `D(w) * inertiaDeg_E(w)` when `w.restrict E = v`, and
   zero otherwise. Filter the support by this restriction condition. This
   filtered set is a subset of `v.fiberOver F`, because `mem_fiberOver`
   characterizes membership by exactly that condition. Every term in the
   fiber outside the filtered set has `D(w) = 0`: otherwise `w` belongs to
   `D.support`, and its fiber membership gives the other required condition.
   Consequently `Finset.sum_subset` extends the sum to the entire finite
   fiber without changing its value. Substituting `D(w) = w.ord f` and
   commuting the integer factors, the resulting sum is
   `∑ w ∈ v.fiberOver F, (w.inertiaDeg E : ℤ) * w.ord f`.
   Child 3 identifies this with `v.ord g`, which equals `A(v)` by step 4.
   This proves the claimed equality of divisors.

6. The pinned library theorem `Divisor.degree_pushforward` states that
   `degree (Divisor.pushforward E D) = degree D`. Its hypotheses are the
   compatible field tower and algebraicity of `F/E`, supplied by step 1.
   In the library it is proved by induction on finitely supported divisors:
   pushforward sends the singleton coefficient `n` at `w` to
   `n * inertiaDeg_E(w)` at the restricted place, and
   `deg(w.restrict E) * inertiaDeg_E(w) = deg(w)` follows from the residue
   tower and `Module.finrank_mul_finrank`. This fact does not assume the
   target principal-divisor property. Apply it and step 5 to obtain
   `degree D = degree (pushforward E D) = degree A = 0`.
   The divisor `D`, its coefficient equality, and this degree equality give
   the required witness for arbitrary nonzero `f`, completing the theorem.

## Pinned library provenance and historical work

The reference manifest pins project commit
`956e8c600d8b95b46948ae5e37b13930b5f3d06b` and mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. The following are existing library
facts in that snapshot, not newly introduced child declarations:

- `project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:179–219` defines
  divisors, degree, and the exact principal-divisor property.
- `project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean:425–479` supplies
  residue-degree multiplicativity, divisor pushforward, degree preservation,
  and its coefficient formula.
- `project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean:438–458` supplies
  the finite fiber and its membership characterization.
- `mathlib/Mathlib/Algebra/CharP/Algebra.lean:77` supplies
  `charZero_of_injective_algebraMap`.
- `mathlib/Mathlib/FieldTheory/Separable.lean:657–665` supplies separability
  of integral extensions of characteristic-zero fields.
- `mathlib/Mathlib/RingTheory/Norm/Basic.lean:112` supplies
  `Algebra.norm_ne_zero_iff` for finite free extensions of domains.
- `mathlib/Mathlib/Data/Finsupp/Defs.lean:274–281` supplies
  `Finsupp.ofSupportFinite` and its defining coefficient equality. The
  support membership, finite sum, and extensionality steps use ordinary
  pinned `Finsupp`, `Finset`, and `Set` infrastructure.

All relative paths above are under the single required snapshot:
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/`.

The accepted `natural-proof-v6.md` and original scaffold are preserved as
history. Their rational-place classification, normalization, determinant,
and localized-length work is implemented by the accepted children and their
tracked descendants. This root directly invokes only the three children
listed above; the final finite regrouping is expressed through the existing
pushforward lemmas. There is no additional geometric obligation or conditional
outline. Integration restores all 49 accepted child declarations from their
recorded candidate commits, retaining each exact globally qualified name and
type, and removes duplicated scaffolds and detached overlay fragments. No
new named helper is introduced. Source compilation, exact-contract comparison,
and transitive axiom auditing remain separate from the controller's independent
review of this final prose.

## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
