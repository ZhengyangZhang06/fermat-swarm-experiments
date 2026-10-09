# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1.place_equivalence_degree-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, E, L, their field and algebra structures, and e. For a place v of E put A = v.toValuationSubring and define B = {y ∈ L | e⁻¹(y) ∈ A}. Since e⁻¹ is a ring homomorphism, B is a subring. Applying the valuation alternative in A to e⁻¹(y), and using e⁻¹(y⁻¹) = e⁻¹(y)⁻¹, shows that y ∈ B or y⁻¹ ∈ B. Thus B is a valuation subring; equivalently it is A.comap e.symm.toRingHom.
2. For k ∈ K, e⁻¹(algebraMap K L k) = algebraMap K E k belongs to A, so B contains the image of K. If B were the whole field L, then for every x ∈ E the element e(x) would belong to B, giving x ∈ A. This would contradict v.ne_top'. Hence B is proper.
3. Restrict e to a ring isomorphism r₀ : A ≃+* B, with inverse the restriction of e⁻¹. These maps land in the stated subrings by the definition of B, and their compositions are identities because e and e⁻¹ are inverse. To prove that B is a principal ideal ring, let I be any ideal of B. Its inverse image J under r₀ is an ideal of A, hence J = (a) for some a ∈ A. The element r₀(a) belongs to I. Conversely, if b ∈ I, then r₀⁻¹(b) ∈ J, so r₀⁻¹(b) = c a for some c ∈ A. Therefore b = r₀(c)r₀(a). These two inclusions give I = (r₀(a)). Thus every ideal of B is principal.
4. The properties in steps 1–3 define a place Tₑ(v) with valuation subring B. The K-algebra structures on A and B are the restrictions of the ambient K-algebra maps. Consequently r₀(algebraMap K A k) = algebraMap K B k, because their ambient values are related by e.commutes and subtype inclusion is injective. Hence r₀ upgrades to a K-algebra isomorphism rᵥ : A ≃ₐ[K] Tₑ(v).toValuationSubring. By construction, (rᵥ(a) : L) = e(a : E).
5. Apply the construction of steps 1–4 to e⁻¹ to obtain a map Tₑ₋₁ from places of L to places of E. For x ∈ E, membership in the valuation subring of Tₑ₋₁(Tₑ(v)) is equivalent to e(x) ∈ B, which is equivalent to x ∈ A. Thus this subring equals A, and Place.ext gives Tₑ₋₁(Tₑ(v)) = v. For a place w of L with subring C, membership of y ∈ L in the subring of Tₑ(Tₑ₋₁(w)) reduces to e(e⁻¹(y)) ∈ C, hence to y ∈ C. Place.ext similarly gives Tₑ(Tₑ₋₁(w)) = w. These maps therefore define an equivalence θ with forward map Tₑ.
6. Fix v and its isomorphism rᵥ. A ring isomorphism preserves and reflects units: it sends a unit and its inverse to mutually inverse elements, and the inverse isomorphism proves reflection. In each local valuation ring the maximal ideal consists of nonunits. Therefore rᵥ carries the maximal ideal of A exactly onto the maximal ideal of B.
7. Define the induced residue-field map by [a] ↦ [rᵥ(a)]. Step 6 makes it well-defined: differences in the first maximal ideal map into the second. The map induced by rᵥ⁻¹ is its inverse, and ring operations descend from those of rᵥ. Since rᵥ commutes with the restricted K-algebra maps and the residue algebra maps are their composites with the quotient maps, this is a K-algebra isomorphism κ(v) ≃ₐ[K] κ(θ(v)). This is precisely the construction supplied by IsLocalRing.ResidueField.mapAlgEquiv.
8. Its underlying K-linear equivalence preserves Module.finrank by LinearEquiv.finrank_eq. That theorem follows from equality of the lifted cardinal ranks and application of Cardinal.toNat, so it requires no finite-dimensionality assumption. Since Place.deg is the finrank of the residue field over K, it follows that (θ(v)).deg = v.deg. The equivalence θ, these degree equalities, and the isomorphisms rᵥ with the compatibility equation from step 4 establish the entire conclusion.

## Key steps

1. Pull each valuation subring back along e.symm and prove it contains K and remains proper.
2. Restrict e and transfer principality of ideals by pulling back an arbitrary ideal and transporting its generator.
3. Upgrade the restriction to a K-algebra isomorphism and use e.symm and Place.ext to obtain an equivalence of places.
4. Transport maximal ideals via preservation and reflection of units, obtaining residue K-algebra isomorphisms.
5. Apply unrestricted finrank invariance to prove preservation of place degrees.

## Reference use

### local-project

Queries:
- `rg -n 'HasPrincipalDivisors|exists_unit_mul_zpow|ord_unit_smul_zpow|mapAlgEquiv' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`
- `grep fallback: def congrEquiv|def congrRingEquiv|congrEquiv_apply|hasPrincipalDivisors.*[Ee]quiv|[Ee]quiv.*[Hh]asPrincipalDivisors`
- `grep fallback: HasPrincipalDivisors|exists_unit_mul_zpow|ord_unit_smul_zpow`
- `grep fallback: mapEquiv|map_residue`
- `grep fallback: (theorem|def) finrank_eq|theorem of_surjective|theorem exists_irreducible|theorem irreducible_iff`
- `#print axioms AlgebraicCurve.Place.ext`
- `#print axioms AlgebraicCurve.Place.exists_unit_mul_zpow`
- `#print axioms AlgebraicCurve.Place.ord_unit_smul_zpow`
- `#print axioms AlgebraicCurve.Divisor.degree_single`
- `#print axioms IsLocalRing.ResidueField.mapAlgEquiv`
- `#print axioms LinearEquiv.finrank_eq`
- `#print axioms IsDiscreteValuationRing.exists_irreducible`
- `#print axioms IsPrincipalIdealRing.of_surjective`
- `#print axioms MulEquiv.irreducible_iff`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/CheckTypes.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/provenance-check.json`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/decomposition-typecheck/name-collision-check.json`

rg was unavailable; searches continued with grep. The project supplies Place.ext, the DVR instance, normalized-order decomposition and evaluation, divisor degree, and analogous automorphism transport proofs. No general cross-field principal-divisor transport theorem or definition of Place.congrEquiv was found; the latter name occurs only in attribute lists. Mathlib supplies valuation-subring comap, residue algebra equivalences, uniformizers, and finrank invariance without finite-dimensionality. Snapshot revisions match project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; pinned dependency tracked trees are clean. Inspected supporting declarations use only propext, Classical.choice, and Quot.sound. Both proposed types elaborate in the existing isolated import-only Submission interface, and proposed names have no detected collisions. The authoritative Submission source still fails on pre-existing unknown attribute targets, so its required import gate remains unsatisfied.
