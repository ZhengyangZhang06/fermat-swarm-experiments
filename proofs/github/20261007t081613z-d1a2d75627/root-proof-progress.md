# Root implementation progress — incomplete

This records the local steps implemented inside the frozen theorem
`WeierstrassCurve.galoisRep_ordinaryLineAt`. It is not the required final proof
and must not be published as a solution. The root retains one inherited proof
placeholder: construction of a nonzero inertia-invariant additive homomorphism
in the multiplicative-reduction case. The good-reduction branch is complete in
the local Lean diagnostics. The whole root remains unproved and unaccepted.

## Implemented argument

1. From primality and `p ≠ 2`, obtain `3 ≤ p` and `Odd p`. The assumption
   `A.LiesOverPrime p` puts the image of `p` in the maximal ideal of `A`.
   Consequently its residue field has characteristic `p`. Reduction of an
   integer is nonzero exactly when that integer is a unit of `A`, and the
   characteristic criterion identifies this with nondivisibility by `p`.

2. For a polynomial `f` over `A` with a unit coefficient in positive degree,
   prove that `f` has a root in `A`. Suppose otherwise and factor its image `F`
   over the algebraic closure. Every root `r` lies outside `A`, so `r⁻¹` lies in
   its maximal ideal. The polynomial product of `1 − r⁻¹ X` is defined over `A`
   and reduces to `1`. Factoring each `X − r` as
   `−r (1 − r⁻¹ X)` and evaluating at zero shows that `f` is its constant
   coefficient times this product. Its reduction is therefore constant,
   contradicting the positive-degree unit coefficient. This also proves the
   required root existence for monic quadratic polynomials.

3. Apply step 2 to the image of `W.preΨ' p`, using the nondivisible coefficient
   from the ordinary alternative and step 1. This gives an integral
   x-coordinate. Apply step 2 again to the monic polynomial
   `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)` to obtain an integral
   y-coordinate satisfying the Weierstrass equation.

4. The nonzero integer discriminant remains nonzero in the algebraic closure,
   so these coordinates give a nonsingular point. The approved declaration
   `Submission.p03_odd_division_detection_68cf3476`, instantiated over
   `AlgebraicClosure ℚ`, proves that this point is killed by `p`. The code checks
   the integer-to-rational-to-algebraic-closure base change explicitly.

5. In the good-reduction case `p ∤ Δ`, step 1 makes the discriminant a unit in
   `A`. Reducing the integral equation gives nonsingular residue coordinates.
   This supplies a p-torsion point on the original curve whose residue
   coordinates are nonsingular. The continuation below constructs specialization
   as a homomorphism and uses this point to prove its restriction is nonzero.

6. Unpack membership in the frozen `inertiaSubgroupIn` as membership in the
   image of the inertia subgroup of the decomposition group. Its defining
   kernel condition proves that the lifted action fixes every residue class.
   In the multiplicative case, semistability and step 1 prove that `c₄` is a
   unit. No Tate-family conversion is asserted by this step.

7. Prove torsion descent under an arbitrary characteristic-zero field extension
   of `AlgebraicClosure ℚ`, for a curve with nonzero discriminant. Detection
   over the larger field puts a torsion
   point's x-coordinate among the roots of the mapped division polynomial.
   Its leading coefficient is `p`, so it is nonzero. Since the polynomial
   splits over the algebraic closure, the x-coordinate comes from that field.
   The same splitting argument applied to the monic y-coordinate quadratic
   descends y. Transport nonsingularity along the injective field map.
   Injectivity of the existing point base-change homomorphism then shows that
   the preimage point is itself killed by `p`. This proves existence of
   p-torsion preimages; the identity case is handled separately.

8. Prove the abstract exponent construction for a commutative group `G`, a
   commutative additive group `E`, a surjection `θ : Additive G →+ E` with kernel generated
   by `q`, an injective map `n ↦ q^n` on integers, and a pth root of `q` in `G`.
   Lift each p-torsion point to `u`; the kernel condition gives `u^p = q^m`.
   Two lifts differ by `q^k`, so their exponents differ by `kp`. Thus `m mod p`
   is independent of the lift. Products of lifts prove additivity, and a pth
   root of `q` supplies a point mapping to `1`, proving nonzeroness. For
   compatible homomorphisms on `G` and `E` fixing `q`, the same representative
   formula proves invariance. This is a conditional algebraic construction;
   the root still needs a Tate presentation for its actual curve.

9. For any additive group `M` and additive homomorphism `f` from the exact
   torsion module, suppose `f` has a nonzero value and is invariant under the
   exact inertia action. Its additive kernel is a `ZMod p` submodule under the
   existing scalar action. A nonzero value proves the kernel is proper.
   Additivity and invariance show `f(σv − v) = 0`, giving the frozen conclusion.
   The good-reduction branch now supplies this homomorphism. Its construction
   for the multiplicative-reduction branch remains the single proof gap.

## Good-reduction construction added in the continuation

For `p ∤ W.Δ`, the implementation now constructs the entire specialization
homomorphism and uses it to prove the frozen conclusion in that branch. All
steps are local to the tracked root declaration. The argument uses the pinned
affine point formulas directly; it does not assume a projective-specialization
theorem or introduce a geometric axiom.

For an affine point satisfying the integral Weierstrass equation, its
x-coordinate belongs to `A` if and only if its y-coordinate does. If one
coordinate were outside `A` and the other inside, divide the equation by the
appropriate power of the outside coordinate. Its inverse lies in the maximal
ideal, and reduction gives `1 = 0`. Define reduction to send a point with
integral coordinates to its residue coordinates, and every other point,
including the identity, to the identity. The discriminant is a unit by the
integer-unit criterion, so the reduced affine points are nonsingular.
The integral negation formula proves compatibility with negation.

To prove additivity, take the three affine intersections of a nonvertical
secant or tangent, counted with multiplicities. Write its slope as `l`, and
use the exact factorization of `addPolynomial` supplied by the pinned affine
formulas. There are two cases.

* If `l` is integral, write the line as `y = l*x + n`. If `n` is integral,
  substitution into the Weierstrass equation gives a monic cubic for every
  x-coordinate. A root outside `A` would again give `1 = 0` after dividing
  by its cube and reducing, so all three points have integral coordinates.
  Reduce both the line equations and the cubic factorization. Comparing the
  quadratic coefficient gives the third x-coordinate in the affine addition
  formula. When the first two reduced points coincide, differentiation of
  the factorization and nonsingularity prove that the reduced line has the
  required tangent slope. Thus the three reduced points sum to zero, also
  when roots coalesce. If `n` is not integral, no point of this line can have
  integral coordinates, and all three reduce to zero.

* If `l` is not integral, let `t = l⁻¹`, which belongs to the maximal ideal,
  and write the line as `x = t*y + n`. A nonintegral `n` again forces all
  three points to reduce to zero. For integral `n`, substitute into the curve
  equation to obtain a polynomial `f` over `A`. Its factorization is
  `-t³*(Y-y₁)*(Y-y₂)*(Y-y₃)`. Its reduction is a monic quadratic, with linear
  coefficient `a₁*n + a₃`. The positive unit-coefficient root lemma gives
  one integral root. Divide by its monic linear factor; the quotient has
  nonunit quadratic coefficient and unit linear coefficient, so the same
  lemma gives a second integral root. The three roots cannot all be
  integral, since their sum times `-t³` would make `f`'s quadratic
  coefficient a nonunit. Thus exactly two roots, counting multiplicities,
  are integral. For these roots `b,d`, coefficient comparison gives
  `f₁ + f₂*(b+d) + (-t³)*(b²+b*d+d²) = 0`. Reducing shows that their
  y-coordinates sum to `-a₁*n-a₃`; their x-coordinates both reduce to `n`.
  The two finite reductions are therefore negatives, and the third point
  reduces to zero.

These computations give the chord identity for all affine pairs that are
not negatives. The pinned `nonsingular_negAdd` and `addPolynomial_slope`
lemmas identify the third intersection for the actual point addition law.
Pairs involving zero or two opposite points follow from preservation of
zero and negation. This proves additivity without excluding tangencies,
coincident reductions, or lines that become vertical after reduction.

An inertia element lifts to the decomposition subgroup, preserves membership
in `A`, and fixes residue coordinates by its kernel condition. Hence it
fixes the reduction of every point. The already constructed integral
p-torsion witness reduces to an affine point and is therefore nonzero.
Restrict the reduction homomorphism to the exact `torsionBy` module and apply
the previously proved proper-kernel construction. This closes the
good-reduction branch of the exact root theorem.

Additional pinned library reuse occurs in
`mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`
(`addPolynomial_slope`, `nonsingular_negAdd`, `map_addPolynomial`, slope and
negation formulas), `Affine/Point.lean` (`add_some`, `add_of_Y_eq`, `neg_some`),
and the polynomial coefficient, derivative, and cubic factorization APIs.
A search of the pinned elliptic-curve directory for `specialization`,
`reductionHom`, `reductionMap`, `tate.uniform`, and `ordinaryLine` returned
no matches. The specialization proof above is implemented locally rather
than attributed to a nonexistent library declaration. The shared
integral-root proof is retained once, with the valuation ring made explicit.

## Dependency and library provenance

The only accepted child called by these new local steps is
`Submission.p03_odd_division_detection_68cf3476`. The accepted Tate theorem and
all 24 child declarations remain unchanged. Their preservation does not imply
that the remaining root argument has been implemented. The accepted natural
proof and historical decomposition records are preserved without edits.

The local-project manifest pins project revision
`81f093181fd6c58dc887fcae5ec8b896996f1885` and mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Within the pinned snapshot:

- `project/Definitions/Def_FLTPrelim_Ramification.lean` defines the exact
  valuation-prime hypothesis and ambient inertia subgroup.
- `project/Definitions/Def_FLTPrelim_Modularity.lean` defines semistability.
- `mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean` supplies
  `coe_mem_nonunits_iff`, `inv_mem_nonunits_iff`, and `nonunits_subset`.
- `mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean` defines inertia
  as the kernel of its residue-field action.
- `mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean` supplies the
  reduction-zero and reduction-unit equivalences.
- `mathlib/Mathlib/Algebra/CharP/Basic.lean` supplies
  `CharP.charP_iff_prime_eq_zero`; the imported characteristic API supplies
  `CharP.intCast_eq_zero_iff`.
- `mathlib/Mathlib/FieldTheory/IsAlgClosed/Basic.lean` and
  `mathlib/Mathlib/Algebra/Polynomial/Splits.lean` supply splitting and
  `Polynomial.Splits.eq_prod_roots` and `Polynomial.Splits.mem_range_of_isRoot`.
- `mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` supplies
  the injective additive point map and its compatibility with multiplication.
- `mathlib/Mathlib/Algebra/Group/TypeTags/Basic.lean` supplies the additive
  translation of multiplication, division, and powers.
- `mathlib/Mathlib/Algebra/Module/ZMod.lean` supplies
  `AddSubgroup.toZModSubmodule`, retaining the contract's module instance.
- `mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean` supplies
  `equation_iff_nonsingular_of_Δ_ne_zero`; the existing base-change and
  division-polynomial map identities transport the equations and roots.

The auxiliary harnesses passed warning-fatal checks for the completed local
steps. The integrated root harness fails with `declaration uses sorry`.
The continuation's complete good-reduction construction passed, and a separate
diagnostic proving the exact root conclusion with the additional assumption
`p ∤ W.Δ` passed with only `propext`, `Classical.choice`, and `Quot.sound`.
That diagnostic declaration exists only in a disposable test file; no new
global helper is added to the solution.
These checks are diagnostics, not configured-comparator acceptance or a
complete transitive-axiom certificate for the root.

## Remaining implementation

The good-reduction branch is now implemented using the specialization
homomorphism above. The multiplicative branch still needs the specified
valuation/completion and inertia-fixed splitting-field construction,
conversion of the curve to the
explicit Tate family, and application of the checked torsion-descent and
exponent constructions to the resulting compatible inertia action. These
are the existing accepted natural-proof route, not new decomposition nodes or
new assumptions. A complete matching `root-final-proof.md` cannot truthfully
be supplied until these obligations are proved in Lean.
