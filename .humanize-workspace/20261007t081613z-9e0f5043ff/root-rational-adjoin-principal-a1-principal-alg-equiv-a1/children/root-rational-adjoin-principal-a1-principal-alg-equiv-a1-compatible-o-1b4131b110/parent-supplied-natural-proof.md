# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1.compatible_order_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated fields, algebra structures, e, v, w and r, and assume the compatibility equation. Write A = v.toValuationSubring and B = w.toValuationSubring. Fix f ∈ E with f ≠ 0. The project's Place instance makes A a discrete valuation ring: A is a proper principal valuation subring. By IsDiscreteValuationRing.exists_irreducible choose π ∈ A with Irreducible π.
2. Put π' = r(π) ∈ B. Ring isomorphisms preserve and reflect units. Thus π' is not a unit, since otherwise π would be one. If π' = ab in B, applying r⁻¹ gives π = r⁻¹(a)r⁻¹(b). Irreducibility of π implies that r⁻¹(a) or r⁻¹(b) is a unit, and applying r implies that a or b is a unit. Therefore π' is irreducible.
3. Put n = v.ord f. By Place.exists_unit_mul_zpow applied to f ≠ 0 and π, there exists u ∈ Aˣ such that f = (u : E)(π : E)^n. Here the ambient value of u means the composite coercion from Aˣ to A to E, and the power is an integer power in E.
4. Transport u to a unit u' ∈ Bˣ by applying r to its value and inverse. The unit identities follow because r preserves multiplication and one. Its value in B is r(u : A). The compatibility hypothesis consequently gives (u' : L) = e(u : E), and also (π' : L) = e(π : E).
5. Apply e to the factorization in step 3. A field isomorphism preserves multiplication, inverses and hence integer powers. Substituting the two equations from step 4 therefore gives e(f) = (u' : L)(π' : L)^n.
6. Apply Place.ord_unit_smul_zpow at w to the unit u', the irreducible π' from step 2, and the integer n. It gives w.ord((u' : L)(π' : L)^n) = n. Rewriting by step 5 and n = v.ord f proves w.ord(e(f)) = v.ord f, as required for every nonzero f.

## Key steps

1. Choose an irreducible uniformizer in the discrete valuation ring of v.
2. Prove that its image under r remains irreducible.
3. Factor f as a valuation-ring unit times the uniformizer raised to v.ord f.
4. Transport the unit and factorization using compatibility with e and preservation of integer powers.
5. Evaluate the transported normalized order with Place.ord_unit_smul_zpow.

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
