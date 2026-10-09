# Final proof of `CerednikDrinfeld.QM.RigidifiedPairClass.exists_ptR_eq`

This handoff describes the argument in `Submission.lean`. The declaration has the
exact binders and conclusion of the frozen source
`Fermat/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_ptR_eq.lean` at project
commit `73257f1e32d99b75813b037f28a5cf45a2db886d`. The original scaffold and
`natural-proof-v4.md` remain historical review records, unchanged. This document
does not assert independent publication-proof review or final DAG acceptance.

## Assumptions and notation

Retain the prime naturals `r` and `rbar`, the nonzero natural `N`, `hrN : ¬ r ∣ N`,
and `hrr : rbar ≠ r`. Retain the commutative rings `𝒪` and `Onr`, their algebra
structure, `π : 𝒪`, and `hunr : Ideal.span {(r : 𝒪)} = Ideal.span {π}`. Retain
`a b : ℚ`, the indefinite quaternion ramification hypothesis `hBq`, the order
submodule `Λ`, its maximality `hΛ`, integer containment `hΛℤ`, the coordinate map
`coord` and `hcoord`, and the fixed fake elliptic curve `A₀` over `Onr/(π)`.
Retain `n`, `hn : 3 ≤ n`, `hrn : ¬ r ∣ n`, the scheme `M`, its structure map
`fM`, the full-level moduli-point function `ptF`, and `hM : IsFineModuli …`.
Retain the Noetherian commutative `𝒪`-algebra `C`, nilpotence hypothesis `hC`,
and `ψ : Onr →ₐ[𝒪] C`.

Write `c = algebraMap 𝒪 C π` and `MC = M ×_(Spec 𝒪) Spec C`. Write `pM` and
`gC` for its first and second projections. Retain the family of schemes `X d`,
the morphisms `ξ d : X d → MC`, and both point functions `tM` and `xOf`, with
all their commutative-ring, algebra, scalar-tower, and compatibility arguments.
In particular, `xOf` has the quotient-domain and incidence equation in the
frozen declaration; it is not replaced by a function on the unreduced ring.
Retain `hmap`, which makes `PR` a functor; `htM`, identifying the first
projection of `tM` with `ptF`; `hx3`, expressing the stated surjectivity of
`ptX` when the image of `c` is zero; and `hxOf`, expressing the stated
naturality of `xOf` for a curve pullback preserving its full-level section and
its rigidification. No stronger version of any of these hypotheses is used.

For a ring homomorphism `f`, write `f* = Spec.map f`. Thus
`(f₂ ∘ f₁)* = f₂* ≫ f₁*`, where `≫` means first the left morphism, then the
right morphism. Degree equalities induce the morphisms `eqToHom (congrArg X h)`.
Proof irrelevance identifies proofs of the same compatibility or degree equality.

## Accepted dependencies actually used

The root directly invokes the following two accepted declarations, with the
precise interfaces retained in `Submission.lean`:

1. `Submission.p07_full_level_quotient_857cd4d38c`: for arbitrary rational
   quaternion parameters, order submodule `Λ`, naturals `N,n`, commutative ring
   `S`, ideal `J`, and `u : WithFullLevel Λ N n S`, it provides a full-level
   curve `v₀` over `S/J`, a morphism `g₀ : v₀.1.A → u.1.A`, the witness
   `IsPullbackVia (Ideal.Quotient.mk J) u.1 v₀.1 g₀`, and the equation
   `v₀.2.P ≫ g₀ = (Ideal.Quotient.mk J)* ≫ u.2.P`. No nilpotence or
   Noetherian assumption is needed for this dependency.
2. `Submission.p07_rigidification_reduction_857cd4d38c`: for arbitrary `Λ,r,N`,
   commutative rings `𝒪,Onr,S` with the stipulated `𝒪`-algebra structures,
   `π`, `A₀`, `ψS : Onr →ₐ[𝒪] S`, a curve `E` over `S`, a curve `V` over
   `S/(algebraMap 𝒪 S π)`, a morphism `g : V.A → E.A` and its curve-pullback
   witness, every rigidification `σ` of `V` for the quotient composite of
   `ψS` yields a rigidification `ρ` of `E` for `ψS`. It gives `ρ.d = σ.d`
   and the exact `Rigidification.IsPullbackVia` witness required by `hxOf`.

The accepted `Submission.p07_curve_ring_equiv_857cd4d38c` is used transitively
by the second declaration, twice. For arbitrary commutative rings `T,U`, a
ring equivalence `k : T ≃+* U`, and a fake elliptic curve `D` over `U`, it
provides a curve `E` over `T`, an isomorphism `i : D.A ≅ E.A`, and curve
pullback witnesses for `k` via `i.hom` and for `k.symm` via `i.inv`.
The rigidification-reduction implementation uses those isomorphisms, composes
the pullback squares, and conjugates the isogeny maps. The root does not assume
that an abstract returned isomorphism is definitionally the identity.

All fifteen accepted child declarations are preserved, including their exact
globally qualified names and frozen types. The remaining children implement
group-law transport, abelian-surface and finite-flat-rank transport, quotient
curve construction, level geometry, full-level pullback, point equivalence,
repeated-sum naturality, pullback composition, and isogeny/level transport.
They are dependencies of the accepted declarations above, not new root lemmas.
The historical prose's elementary quotient-idempotence “Lemma A” is implemented
by local calculations and existing library declarations. No additional named
theorem is introduced by the root implementation.

## Proof

1. Fix an arbitrary commutative ring `S` with its stipulated `C`- and
   `𝒪`-algebra structures and scalar tower, a map `ψS`, its compatibility proof
   `hψS`, and `z : PR(S)`. By `Quot.ind`, it suffices to handle a representative
   `p`. The definition of `Pt` gives data `p.t : Spec S → MC`, `p.d : ℕ`, and
   `p.x : Spec T → X p.d`, where
   `J = Ideal.span {algebraMap C S c}` and `T = S/J`. Their equations are
   `p.t ≫ gC = (C → S)*` and `p.x ≫ ξ p.d = q* ≫ p.t`, for the quotient
   `q : S →ₐ[C] T`. This reduction uses no property of the relation defining
   the quotient.

2. Give `T` its induced algebras. Put `ψT = (q.restrictScalars 𝒪).comp ψS`.
   Substituting `hψS` and using `q.commutes` proves the exact compatibility
   `hψT` with `ψ`. The generator of `J` belongs to `J`, so its image in `T`
   is zero, by `Ideal.Quotient.eq_zero_iff_mem` and `Ideal.subset_span`.
   This is the hypothesis `h0 : algebraMap C T c = 0` needed by `hx3`.

3. The pullback relation for `MC`, the equation for `p.t`, and the scalar-tower
   identity show `(p.t ≫ pM) ≫ fM = (𝒪 → S)*`. Apply
   `hM.ptF_surjective` to this point over `Spec 𝒪`. Obtain a full-level curve
   `u` over `S` with underlying moduli morphism `ptF(S,u) = p.t ≫ pM`.
   By `htM`, `(tM S u).1` and `p.t` have the same first projection. They have
   the same second projection by their over-base equations. Pullback
   extensionality therefore gives `htu : (tM S u).1 = p.t`.

4. Composing the incidence equation for `p.x` with `gC` gives
   `p.x ≫ (ξ p.d ≫ gC) = (C → T)*`. Here the induced algebra map to `T`
   is the composite with `q`, and contravariance of `Spec` identifies the
   composites. Apply `hx3` to this `SchemeHomOver` point, using `ψT,hψT,h0`.
   Obtain a full-level curve `v` over `T`, a rigidification `σ` of `v`, an
   equality `hd : σ.d = p.d`, and the asserted equality of `ptX` with `p.x`.

5. Let `K = Ideal.span {algebraMap C T c}`, `U = T/K`, and `k : T → U`
   be the quotient map. By `h0`, `K = ⊥`. The ring equivalence
   `e : U ≃+* T` is the composition of `Ideal.quotEquivOfEq` with
   `RingEquiv.quotientBot T`. The pinned model's `quotEquiv_comp_mk` gives
   `e.toRingHom.comp k = RingHom.id T`; hence `e* ≫ k* = id`.
   Unfolding the actual definition of `ptX`, the equality from step 4 says
   `e* ≫ (xOf T ψT hψT v σ).1 ≫ θhd = p.x`, where `θhd` is the degree
   transport. This explicitly accounts for the second quotient in `ptX`.

6. For any equality `h : i = j`, substitution shows
   `eqToHom (congrArg X h) ≫ ξ j = ξ i`. Compose the equation of step 5
   with `ξ p.d`, apply this identity, and use the defining incidence equation
   of `xOf`. The left side becomes `e* ≫ k* ≫ (tM T v).1`, and cancellation
   from step 5 gives
   `(tM T v).1 = p.x ≫ ξ p.d = q* ≫ p.t`.

7. Apply the accepted full-level quotient theorem to `u` and `J`. It gives
   `v₀,g₀,hg₀,hP₀` as stated above. Unpacking `hg₀` and adjoining `hP₀`
   gives exactly `WithFullLevel.IsPullback q u v₀`. The quotient's induced
   `𝒪`-algebra structure gives `q* ≫ (𝒪 → S)* = (𝒪 → T)*`.
   Thus `hM.ptF_pullback` identifies `ptF(T,v₀)` with `q* ≫ ptF(S,u)`.
   By steps 3 and 6 and `htM`, `ptF(T,v)` has that same underlying morphism.
   Subtype extensionality gives equality of the two moduli points.

8. Apply `hM.ptF_injective`. The resulting full-level isomorphism supplies
   `i : v.1.A ≅ v₀.1.A` over `Spec T`, preserving multiplication and the
   `Λ`-action, identifying level-factorization conditions in both directions,
   and satisfying `v.2.P ≫ i.hom = v₀.2.P`. Define `g = i.hom ≫ g₀`.
   Transport the pullback square of `hg₀` along `i` using `IsPullback.of_iso'`.
   This makes the square for `g` cartesian. Composing the multiplication
   equations for `i` and `g₀` proves multiplication compatibility. Composing
   their action equations proves action compatibility. A point factoring
   through `v`'s level scheme factors through `v₀`'s after applying `i`, then
   through `u`'s after applying `g₀`. These give every field of
   `hg : IsPullbackVia q u.1 v.1 g`. The section equations also compose to
   `hP : v.2.P ≫ g = q* ≫ u.2.P`.

9. The scalar tower identifies `algebraMap 𝒪 S π` with `algebraMap C S c`.
   Consequently its generated ideal is `J`. Rewrite the accepted
   rigidification-reduction theorem along this ideal equality and apply it
   to `u.1,v.1,g,hg,σ`. This yields a rigidification `ρ` of `u.1` for `ψS`
   and the exact rigidification-pullback witness `hρ` along `q`. The quotient
   algebra maps agree with the maps used to define `ψT`; the rewrite changes
   neither the ring nor the required pullback data.

10. Apply `hxOf` to `S,T,q,ψS,hψS,hψT,u,v,ρ,σ,g,hg,hP,hρ`.
    It supplies `hnat : σ.d = ρ.d` and
    `(xOf T ψT hψT v σ).1 ≫ θnat = qbar* ≫ (xOf S ψS hψS u ρ).1`,
    where `qbar = RigidifiedPairClass.qmap c q`. Ring-homomorphism
    extensionality on quotient representatives proves `qbar = k`: both
    send the class of `s` to the class of `q(s)`. Hence `e* ≫ qbar* = id`.

11. Put `hρd = hnat.symm.trans hd : ρ.d = p.d`. The degree transports satisfy
    `θnat ≫ θρd = θhd`. This follows from `eqToHom_trans` and proof
    irrelevance, or directly by substituting the equal indices. Compose
    step 10 on the left with `e*` and on the right with `θρd`. Using
    associativity, cancellation from step 10, and the equality in step 5,
    obtain
    `(xOf S ψS hψS u ρ).1 ≫ θρd = p.x`.

12. The representative of `ptR(S,ψS,hψS,u,ρ)` has components
    `(tM S u).1`, `ρ.d`, and `(xOf S ψS hψS u ρ).1`. They agree with those
    of `p` by `htu`, `hρd`, and step 11, including the necessary transport
    of the third component. The model's `Pt.ext'` proves equality of the
    representatives; its remaining fields are propositional. Apply
    `congrArg (Quot.mk _)`. The resulting equality is precisely
    `ptR(S,ψS,hψS,u,ρ) = z`. These are the two existential witnesses, for
    arbitrary `S,ψS,hψS,z`, proving the full frozen conclusion.

The proof uses `hM,htM,hx3,hxOf` directly, and retains `hmap` in the definitions
of `PR` and `ptR`. The additional arithmetic, coordinate, maximal-order,
Noetherian, and nilpotence hypotheses remain in the theorem unchanged; this
argument needs no further consequence of them. None of the accepted dependencies
appeals to the root theorem, which is declared after them.

## Pinned library provenance and reference use

Exactly one research source is used: **local-project**, snapshot
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89`.
Its `manifest.json` pins project `73257f1e32d99b75813b037f28a5cf45a2db886d`
and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

- `project/Definitions/Def_CerednikDrinfeld_RigidifiedPairClassModel.lean`:
  inspected `Pt`, `Pt.ext'` (line 24), `qmap` (42), `quotEquiv_comp_mk` (114),
  `ptX` (121), `PR`, and `ptR` (193). These supply the precise quotient
  domains, incidence equations, transport convention, and final extensionality.
- `project/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean`: inspected
  `WithFullLevel.Iso`, `WithFullLevel.IsPullback`, and all four `IsFineModuli`
  fields. The proof uses surjectivity, pullback compatibility, and injectivity;
  it does not need `ptF_iso`.
- `project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean:31` and
  `project/Definitions/Def_CerednikDrinfeld_QMRigidification.lean:63,115`:
  the curve pullback, rigidification, and rigidification-pullback interfaces.
- `mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean:105`:
  `IsPullback.of_iso'`; the pullback uniqueness API supplies `pullback.hom_ext`.
- `mathlib/Mathlib/AlgebraicGeometry/Scheme.lean:483,488`: `Spec.map_id` and
  contravariant `Spec.map_comp`. The quotient and ring-equivalence APIs supply
  the elementary zero-ideal equivalence, ideal-membership criterion, and
  quotient extensionality used explicitly above.

Queries included `exists_ptR_eq|ptF_surjective|ptF_injective|ptF_pullback|quotEquiv_comp_mk|qmap_comp_mk`
in the snapshot's Cerednik–Drinfeld definition files, and
`theorem of_iso.|lemma of_iso.|theorem hom_ext|lemma hom_ext` in its mathlib
pullback directory. Searching the inspected model and fine-moduli files for
`sorry|admit|axiom|exists_ptR_eq` found no matches. No upstream root solution
or network source was acquired. Source inspection supplies provenance; the
configured comparator supplies the separate compatibility, exact-type,
kernel, clean-dependency, and transitive-axiom evidence.
