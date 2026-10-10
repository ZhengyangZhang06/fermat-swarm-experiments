# Final proof of the frozen root theorem

The declaration proved in `Submission.lean` is exactly
`GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius`.
This document explains its actual argument. The original scaffold and
`natural-proof-v124.md` remain historical, unchanged records. The root uses the
selected, comparator-approved dependencies, not a new decomposition.

## Assumptions and notation

Put Ω = AlgebraicClosure ℚ and G = Autℚ(Ω). All automorphism and endomorphism
products apply the right factor first. Let 𝒪 be the characteristic-zero
commutative discrete valuation domain in the statement, complete for powers of
its maximal ideal 𝔫. Let p be the given prime with p ∈ 𝔫. Let R be the given
commutative local 𝒪-algebra, finite as an 𝒪-module, and let its structure map
f : 𝒪 → R be local, as stipulated by `hl`. Write 𝔪 = maximalIdeal R.

The representation ρ has its given finite free R-module V, rank two, action
B : G → End_R(V), and maximal-ideal-adic continuity. Write t(g) = trace_R(B(g));
this is definitionally `ρ.trace g`. Let Y have exactly the given additive
commutative group, R-module and 𝒪-module structures, compatible scalar tower,
and finite generation over 𝒪. Put A = ρY. Its assumed continuity says that for
every n there is a finite-degree intermediate field FY of Ω/ℚ such that
(A(δ) − 1)y ∈ (pR)^nY whenever δ fixes FY pointwise.

Retain L with `NeZero L`, hence L > 0, the monoid homomorphism
D : (ZMod L)ˣ → End_R(Y), the commutation hypothesis `hD`, the finite set S₀,
and every quantifier in `hES`. The latter supplies
A(τ)^2 − t(τ)A(τ) + ℓD(uℓ,L) = 0 for every allowed arithmetic Frobenius τ
at every valuation subring above a prime ℓ outside S₀, different from p and
not dividing L. Here uℓ,L is exactly `ZMod.unitOfCoprime` with the coprimality
proof in the frozen statement. For an ideal J, JM denotes the submodule
`J • (⊤ : Submodule R M)`, not an additional topology or finite quotient.

Rank two and `hD` remain in the exact statement. The transfer argument does not
need their content; finite freeness of V is needed for trace congruence. No
finite-residue-field hypothesis, freeness of Y, or completeness of R is added.

## Approved dependencies actually used

All names below have prefix `Submission.p09_af497904fe_` in the integrated
source. The six direct dependencies are:

1. **`adic_cyclotomic_character`.** Under the stated hypotheses on 𝒪, p and
   the local map to R (without requiring R finite over 𝒪), it gives a
   homomorphism c : G → Rˣ. For each n, agreement on some finite-degree field
   Fc implies c(σ) − c(τ) ∈ 𝔪^n. For every prime ℓ ≠ p, valuation subring P
   above ℓ and arithmetic Frobenius τ at P, it gives c(τ) = ℓ in R.
2. **`finite_cyclotomic_character`.** For every nonzero N, it gives a
   homomorphism G → (ZMod N)ˣ determined by agreement on a finite-degree
   intermediate field. Its action on every Nth root of unity is exponentiation
   by that residue class; at every arithmetic Frobenius above a prime ℓ not
   dividing N its value is uℓ,N. The root uses N = L and the finite-field and
   Frobenius clauses.
3. **`frobenius_approximation`.** For every finite-dimensional Galois
   intermediate field E of Ω/ℚ, σ ∈ G and finite B₀ ⊆ ℕ, there exist a prime
   ℓ ∉ B₀, a valuation subring P of Ω above ℓ and arithmetic Frobenius τ at P
   agreeing with σ on E. This is the accepted arithmetic dependency. Its
   hypotheses involve no representation, coefficient ring or quadratic relation.
4. **`action_congruence`.** For any commutative ring C, C-module M, ideal J,
   action U : G → End_C(M) and intermediate field F, if (U(δ) − 1)M ⊆ JM
   for every δ fixing F, then agreement of σ and τ on F gives
   (U(σ) − U(τ))M ⊆ JM. Neither F nor M needs finiteness for this lemma.
5. **`trace_congruence`.** For a finite free module W over a commutative ring C,
   ideal J and u,v ∈ End_C(W), the inclusion (u − v)W ⊆ JW implies
   trace(u) − trace(v) ∈ J.
6. **`quadratic_congruence`.** For any C-module M over a commutative ring,
   ideal J, endomorphisms a,b,d, and scalars s,r,u,v, if (a − b)M ⊆ JM,
   s − r ∈ J and u − v ∈ J, then
   ((a² − sa + ud) − (b² − rb + vd))M ⊆ JM. No endomorphism commutation is
   required.

The other two immediate accepted root children, `adic_character_lift` and
`finite_inverse_limit`, are retained with their exact globally qualified names
and types. They are infrastructure for the accepted character and Frobenius
constructions, respectively, and are not called directly by this root proof.
The adic lift constructs a unique unit-valued character from compatible
approximate multiplicative characters in a complete separated ideal-adic ring.
The inverse-limit lemma gives a coherent family in any sequence of nonempty
finite sets with coherent restriction maps; surjectivity is not assumed.

The historical arithmetic decomposition, including the ray-class and analytic
lemmas and the separately tracked `rhc_20261009_adic_cyclotomic_character`, is
retained as accepted dependency material. These are not new helpers introduced
by the root. The proof below invokes the final Frobenius approximation theorem
with all its hypotheses, rather than leaving a geometric or arithmetic
obligation open. All intermediate statements introduced in the root Lean proof
are local proof steps, not new globally named theorems.

## Proof

1. **Finiteness, separation and comparison of ideals.** A discrete valuation
   domain is a principal ideal ring and therefore Noetherian. Since R is finite
   over 𝒪, `IsNoetherianRing.of_finite 𝒪 R` makes R Noetherian. Since Y is
   finite over 𝒪 and the scalar tower is compatible,
   `Module.Finite.of_restrictScalars_finite 𝒪 R Y` makes Y finite over R.
   Krull intersection for a finite module over a Noetherian local ring gives
   ⋂ₙ𝔪^nY = 0. Its proper-ideal premise holds because 𝔪 is maximal.
   Locality of f gives f(p) ∈ 𝔪, and f(p) = p by preservation of natural
   casts. Thus pR ⊆ 𝔪, so (pR)^nY ⊆ 𝔪^nY for every n, including zero.

2. **Fix the witnesses.** Apply `adic_cyclotomic_character` with p, hp𝒪 and
   hl to obtain c. Apply `finite_cyclotomic_character` with N = L to obtain
   χ : G → (ZMod L)ˣ and its finite-degree controlling field Fχ. These two
   homomorphisms are fixed once, before any choice of σ, precision, or prime.
   For each g define the endomorphism
   Q(g) = A(g)^2 − t(g)A(g) + c(g)D(χ(g)). Coercions of unit values to R are
   understood only in scalar expressions.

3. **Choose one controlling Galois field.** Fix arbitrary σ ∈ G, n ∈ ℕ and
   y ∈ Y. Choose FY from hcont at precision n, Fρ from ρ's adic continuity
   at n, and Fc from the continuity clause for c. Form the compositum
   F = ((FY ∨ Fρ) ∨ Fc) ∨ Fχ inside Ω, and let E be its normal closure over
   ℚ inside Ω. Each of the four fields is finite-dimensional, so successive
   finite composita and then the normal closure are finite-dimensional.
   The algebraic closure Ω is normal over ℚ; normality of E follows from
   the normal-closure construction. Characteristic zero gives separability,
   hence E/ℚ is Galois. The inclusion F ⊆ E is the standard
   `IntermediateField.le_normalClosure` inclusion.

4. **Choose an allowed Frobenius.** Let
   B₀ = S₀ ∪ ({p} ∪ {0,1,…,L}). It is finite. Apply the approved
   Frobenius approximation to E, σ and B₀. It gives ℓ, P and τ with ℓ prime,
   ℓ ∉ B₀, P lying over ℓ, τ arithmetic Frobenius at P, and τ|E = σ|E.
   In particular ℓ ∉ S₀ and ℓ ≠ p. If ℓ divided L, positivity of L would
   imply ℓ ≤ L, putting ℓ in B₀, a contradiction. Thus ℓ does not divide L.
   Restricting equality on E gives σ = τ on FY, Fρ, Fc and Fχ; the Lean
   proof reverses the equality from the approximation theorem as needed.

5. **Obtain all congruences.** Apply `action_congruence` to A with ideal
   (pR)^n, field FY and the exact pointwise-fixing premise from hcont.
   By Step 1 this yields (A(σ) − A(τ))Y ⊆ 𝔪^nY. Apply the same lemma to B
   with ideal 𝔪^n and field Fρ, using ρ's adic continuity. Then apply
   `trace_congruence` on its finite free module V to obtain
   t(σ) − t(τ) ∈ 𝔪^n. Agreement on Fc gives c(σ) − c(τ) ∈ 𝔪^n,
   while the Frobenius clause gives c(τ) = ℓ, so c(σ) − ℓ ∈ 𝔪^n.
   Finally, agreement on Fχ gives χ(σ) = χ(τ).

   The action lemma is valid without normality of each controlling field:
   δ = τ⁻¹σ fixes that field and U(σ) − U(τ) = U(τ)(U(δ) − 1).
   Every C-linear endomorphism preserves JM. Trace congruence follows by
   choosing a finite free basis: coordinate functionals carry JW into J,
   hence every diagonal coefficient of u − v lies in J and so does their
   sum. These are precisely the operations used in the accepted dependencies.

6. **Use the assumed quadratic relation.** By the finite character's
   Frobenius clause, χ(τ) is exactly uℓ,L. Consequently hES, with the prime
   exclusions from Step 4 and the supplied P and τ, gives
   A(τ)^2 − t(τ)A(τ) + ℓD(χ(σ)) = 0. This rewriting uses χ(σ) = χ(τ);
   the coprimality witness is the one specified in the frozen theorem.

7. **Transfer at the chosen precision.** Apply `quadratic_congruence` with
   J = 𝔪^n, a = A(σ), b = A(τ), d = D(χ(σ)), s = t(σ), r = t(τ),
   u = c(σ), v = ℓ. Step 5 supplies each of its three congruence hypotheses.
   Its conclusion says that the difference between Q(σ) and the zero
   endomorphism in Step 6 sends y into 𝔪^nY. Hence Q(σ)y ∈ 𝔪^nY.
   Algebraically the difference expands, in the stated multiplication order,
   as a(a−b) + (a−b)b − s(a−b) − (s−r)b + (u−v)d. Each summand has
   image in JY, using preservation of JY by a and scalar closure. Thus no
   hidden commutation or invertibility assumption is used.

8. **Pass from all precisions to equality.** The preceding construction works
   for every n ∈ ℕ, including n = 0, with the fixed c and χ. For every y,
   Q(σ)y lies in ⋂ₙ𝔪^nY = 0 by Step 1, so Q(σ)y = 0. Extensionality of
   linear maps gives Q(σ) = 0. Since σ was arbitrary, the fixed c and χ
   satisfy the frozen conclusion for every element of G. The argument also
   covers L = 1 and the zero module Y.

## Pinned library provenance and reference use

`reference_use` has exactly one source entry: **local-project**. Its snapshot is
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596`.
The manifest pins project `20574e45daf714e745af8e649c7b61b21eed5644` and mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. Read-only Git checks found those HEADs
and clean tracked source trees. Their toolchain files name v4.33.1 and v4.33.0,
respectively; actual candidate compatibility is checked using the configured
v4.33.1 verifier, not inferred from source inspection.

Paths below are relative to that snapshot; these are existing library results,
not additional invented helpers:

- `project/Definitions/Def_GaloisRep_Adic.lean:9–28,44–46` supplies the exact
  maximal-ideal-adic continuity, finite free representation, and trace definition.
- `mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` supplies the
  principal ideal ring structure; `RingTheory/PrincipalIdealDomain.lean` supplies
  Noetherianity. `RingTheory/Noetherian/Basic.lean:340` is
  `IsNoetherianRing.of_finite`.
- `mathlib/Mathlib/RingTheory/Finiteness/Basic.lean:301` is
  `Module.Finite.of_restrictScalars_finite`.
- `mathlib/Mathlib/RingTheory/LocalRing/RingHom/Basic.lean:66` is `map_nonunit`.
  Ideal span membership, monotonicity of powers and `Submodule.smul_mono_left`
  implement the ideal comparison.
- `mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:78` supplies
  finite-dimensional composita. `FieldTheory/Normal/Closure.lean:167,173,230`
  supplies normality, finite dimension and containment in the normal closure.
  Algebraic-closure normality and characteristic-zero separability supply the
  corresponding instances without changing imports.
- `mathlib/Mathlib/RingTheory/Filtration.lean:426–429` is
  `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`, with the proper maximal ideal,
  finite R-module Y and Noetherian local R verified in Step 1. This library
  result is Krull intersection, proved through Artin–Rees and Nakayama.

The snapshot was searched with `rg` for `structure GaloisRepAdic`, `def trace`,
`iInf_pow_smul_eq_bot_of_isLocalRing`, finite-dimensional composita and normal
closures, `of_restrictScalars_finite`, `IsNoetherianRing.of_finite` and
`map_nonunit`; the listed files were inspected. The scoped search
`Chebotarev|chebotarev|p09_af497904fe_|frobenius_approximation` returned **no
matches** in `project/Definitions` or `mathlib/Mathlib/NumberTheory`.
Frobenius approximation is therefore explicitly supplied by the accepted child,
not attributed to an unlocated library theorem. No network research was used.

## Source integration and verification boundary

The root sits after its accepted dependencies so Lean can reference them.
Repeated identical overlay commands were removed while keeping one exact
accepted declaration for every child. A misplaced duplicate header inside the
historical adic-character child was removed to reconnect its accepted statement
and accepted proof. A scoped overlapping-instance lint exception preserves that child's redundant
frozen hypotheses; it changes no type or kernel check. No new globally named
helper, axiom or assumption was added.
Every accepted child interface is checked against its controller-frozen type,
including children not directly called by this root.

The original Submission header, frozen contract, problem record and reviewed
handoffs are unchanged. Disposable compiler copies may omit only the two
negative-attribute directives allowed by the operator policy with SHA256
`96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96`;
target absence is checked by Lean. This treatment changes no mathematical input.
Warning-fatal compilation is diagnostic; exact-contract, dependency, kernel and
transitive-axiom acceptance belong to the configured comparator. The independent
final prose review, fresh reviewer comparator, publication and DAG transition
remain outer-controller tasks. This prose does not claim those later approvals.
