# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the fields, algebra structures, isomorphism e and principal-divisor hypothesis. For a project place v of E, let A be its valuation subring and let A' = e(A) inside L. The image is a subring, and for every y in L the valuation alternative for e⁻¹(y) shows that y or y⁻¹ belongs to A'. It contains the image of K because e is a K-algebra map. It is proper because e is bijective and A is proper. Restriction of e gives a ring isomorphism A ≃ A'. Pulling back an ideal of A' along this isomorphism gives a principal ideal of A; the image of a generator generates the original ideal. Thus A' is a principal ideal ring and defines a project place Θ(v) of L.

2. Apply the same construction to e⁻¹. The resulting valuation subrings are inverse images of the original image subrings, so they recover the original subrings exactly. Place.ext then gives inverse maps on project places. Consequently Θ is a bijection from Place K E to Place K L. Restriction of e is also a K-algebra isomorphism of the associated valuation rings, since their K-algebra maps are obtained by restricting those of the ambient fields.

3. A ring isomorphism preserves units. In a local ring the maximal ideal is the set of nonunits, so the restricted isomorphism sends the maximal ideal of v's ring onto that of Θ(v)'s ring. It therefore induces a K-algebra isomorphism of their residue fields. The underlying K-linear equivalence preserves Module.finrank, including when the spaces are not finite-dimensional. By the definition of Place.deg, this proves Θ(v).deg = v.deg.

4. Show that normalized orders are preserved on nonzero elements. The proper principal valuation ring of v is a discrete valuation ring, so choose an irreducible uniformizer π in it. Its image π' in the ring of Θ(v) is irreducible because ring isomorphisms preserve irreducibility. For f ≠ 0, Place.exists_unit_mul_zpow gives f = uπ^n with u a unit and n = v.ord(f), interpreted in E. Applying e gives e(f) = e(u)(π')^n in L; the restricted isomorphism carries u to a unit. Place.ord_unit_smul_zpow at Θ(v) then gives Θ(v).ord(e(f)) = n = v.ord(f).

5. Fix h ≠ 0 in L and put f = e⁻¹(h), which is nonzero by injectivity. The principal-divisor hypothesis supplies a divisor D on Place K E with D(v) = v.ord(f) for every v and degree D = 0. Define D' on Place K L by D'(Θ(v)) = D(v). This is well-defined because Θ is bijective, and its support is the image under Θ of the finite support of D. Hence D' is a divisor. For w = Θ(v), step 4 gives D'(w) = v.ord(f) = w.ord(h), proving the required coefficient formula at every place.

6. Express each divisor as its finite sum of singleton divisors. Reindexing this sum through Θ and using Divisor.degree_single together with step 3 gives degree D' = Σ_v D(v) Θ(v).deg = Σ_v D(v) v.deg = degree D = 0. Thus every nonzero h in L has the required divisor. These witnesses establish HasPrincipalDivisors K L.

## Key steps

1. Transport valuation subrings, properness, constants and principal ideals through the algebra isomorphism.
2. Use the inverse isomorphism and Place.ext to obtain a bijection of project places.
3. Identify residue fields as K-algebras and preserve their finranks.
4. Transport unit-times-uniformizer-power expressions to preserve normalized orders.
5. Reindex each source principal divisor along the place bijection.
6. Preserve finite support, coefficients and degree to obtain the target witnesses.

## Reference use

### local-project

Queries:
- `rg -n 'HasPrincipalDivisors|exists_unit_mul_zpow|ord_unit_smul_zpow|algEquivOfTranscendental' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`
- `HasPrincipalDivisors|hasPrincipalDivisors_of_transcendental|exists_unit_mul_zpow|ord_unit_smul_zpow|congrEquiv`
- `namespace RationalFunctionField|hasPrincipalDivisors|def congrEquiv|theorem.*congr|RatFunc.*adjoin|adjoin.*RatFunc`
- `hasPrincipalDivisors|HasPrincipalDivisors`
- `def algEquivOfTranscendental`
- `theorem eq_of_le_of_ne_top|lemma eq_of_le_of_ne_top`
- `p06_9e0f5043ff_rational_model_principal|p06_9e0f5043ff_principal_alg_equiv`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/FieldTheory/RatFunc/AsPolynomial.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Localization/FractionRing.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1/decomposition-typecheck/CheckAssemblyLibrary.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1/decomposition-typecheck/Submission.frozen-source-check.log`

The handoff confirms that the supplied theorem is the depth-1 rational-adjoin child, while the frozen root retains its characteristic-zero and finite-extension assumptions. rg was unavailable; searches therefore used grep. DivisorClassGroup supplies the exact place, normalized-order, degree and HasPrincipalDivisors definitions. No principal-divisor theorem matched the searched mathlib RatFunc directory, and no general principal-divisor transport theorem was found in the project definitions. The pinned library supplies polynomial transcendental evaluation, fraction-field equivalences and the generated intermediate field's fraction-ring structure, so evaluation needs no new wrapper theorem. Snapshot revisions and all nine dependencies match their manifests and have clean tracked files; the three imported project modules are byte-identical to the snapshot. Audited supporting declarations have only propext, Classical.choice and Quot.sound as transitive axioms. Both proposed types passed a warning-free isolated import-only Submission interface check, including a definitional check that the fraction field's K-algebra map factors through Polynomial.C. IMPORTANT: the unchanged actual Submission fails on three pre-existing unknown attribute targets. Thus actual import Submission validation remains an activation blocker; neither comparator acceptance nor completion of that gate is claimed. Proposed names have no source or active-DAG collisions.
