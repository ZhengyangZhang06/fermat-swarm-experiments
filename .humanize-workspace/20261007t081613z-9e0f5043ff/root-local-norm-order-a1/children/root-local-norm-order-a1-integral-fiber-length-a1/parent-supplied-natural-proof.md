# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1`
- Child DAG node: `root.local_norm_order-a1.integral_fiber_length-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all hypotheses, including n and length_A(C) = n for C = B/bB. The project place ring A is a proper DVR with fraction field E. Choose a uniformizer π and write k = A/(π). The pinned integral-closure theorems apply because A is a Noetherian integrally closed PID and L/E is finite separable, with injective compatible maps. They make B a finite free A-module, a Dedekind domain, and a subring of L having fraction field L. The stated length equality says that C has finite A-length n.

2. Every maximal ideal q of B is nonzero and contracts to (π). To see nonzeroness, the intersection of B with the embedded E is A: an element of E lying in B is integral over A, so belongs to A by integral closedness. If B were a field it would contain π⁻¹, contradicting this intersection. Thus B is not a field, and its zero ideal cannot be maximal. Choose nonzero t ∈ q. Among monic equations for t over A choose one of least degree. Its constant coefficient c_0 is nonzero; otherwise the equation factors as t times a monic equation of smaller degree, and cancellation of t in L gives a contradiction. The equation gives c_0 ∈ q ∩ A. This contraction is a proper prime containing a nonzero element, so in the DVR A it is exactly its maximal ideal (π).

3. Let Q be the set of maximal ideals of B. Since B is Dedekind and is not a field, Q is identified with HeightOneSpectrum B. The existing Place.fiberEquiv identifies HeightOneSpectrum B with the places w satisfying w.restrict E = v. Its source is finite by Place.finite_setOf_restrict_eq, so Q is finite. The same project correspondence identifies the valuation ring of the corresponding w with B_q inside L, using Place.toValuationSubring_eq_of_restrict_eq. The localization is a DVR by IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain, since q is nonzero. These are existing results from the pinned PlacesOverDVR and DedekindDomain/Dvr files and require no principal-divisor hypothesis.

4. For q ∈ Q, give B/q its k-algebra structure induced by A → B → B/q; this is defined because q contracts to (π). If B has A-rank r, reduction of an A-basis gives a k-basis of B/πB with r elements. Since πB is contained in q, the quotient B/q is a quotient of this finite-dimensional vector space. Define f_q = dim_k(B/q), which is finite.

5. For the place w corresponding to q, the residue field of B_q is canonically isomorphic to B/q. Explicitly, send a localized fraction a/s, with s outside q, to the quotient of the images of a and s in the field B/q. This respects equality of fractions, since a cross-multiplied equality becomes the same equality modulo q; the denominators have nonzero, hence invertible, images. The map is surjective because fractions with denominator 1 lift every residue class, and its kernel consists precisely of fractions with numerator in q, namely qB_q. It therefore induces the asserted residue-field isomorphism.

6. The isomorphism in step 5 respects the residue action from A. Both routes take a ∈ A to its image in B_q and then reduce modulo qB_q. Under w.restrict E = v, this is exactly the project's restrictResidueMap E w: its defining formula reduces restrictInclusion on elements of O_v. Thus, after transporting the equality of the downstairs places, the residue-field isomorphism is k-linear for the canonical algebra defining inertiaDeg. It follows that f_q = w.inertiaDeg E. Likewise, normalized order on B_q equals w.ord on L: their valuation rings are identical, and factoring a nonzero element as a unit times an integer power of a uniformizer gives the same exponent for both orders. In particular the image of b is nonzero, belongs to B_q, and has order m_q ∈ ℕ.

7. Choose a B-submodule chain in C of maximum possible length. Such a maximum exists because every strict B-submodule chain is also a strict A-submodule chain and thus has at most n steps. A maximal-length chain begins at zero and ends at C, since otherwise an endpoint could be added. Every successive quotient is simple, since a nonzero proper submodule of such a quotient would refine the chain. This yields a finite B-composition series, including the empty series when C is zero.

8. Each simple factor S of this series is B/q for a unique q ∈ Q. Choose a nonzero s ∈ S. Its cyclic B-submodule is nonzero and hence is S, so B → S, a ↦ as, is surjective. Its kernel q is maximal by simplicity, giving S ≅ B/q. The ideal is uniquely determined because it is the annihilator of B/q and annihilators are preserved by B-module isomorphisms. Let c_q be the number of factors with this ideal.

9. The A-length of B/q is f_q. Indeed, its A-action factors through the surjection A → k, so its A-submodules are exactly its k-linear subspaces. A flag in a finite-dimensional vector space has at most its dimension many strict inclusions, and a basis supplies a flag attaining that bound. Thus its length is dim_k(B/q). Length additivity in each short exact sequence of the composition series, using Module.length_eq_add_of_exact from the pinned Length.lean, gives n = ∑_{q∈Q} c_q f_q. This equality initially holds after casting to ℕ∞; all terms are finite, so injectivity of the natural-number cast gives the equality in ℕ.

10. Fix q ∈ Q and localize the composition series at B minus q. Localization is exact. For kernel exactness, if x/s maps to zero then some allowed denominator t kills the image of x, so tx lies in the original kernel; an original preimage of tx, divided by ts, lifts x/s. The same zero-fraction criterion proves preservation of injectivity, and surjectivity follows by lifting numerators. Applied to B → B/bB, this also identifies C_q with B_q/bB_q.

11. If a composition factor is B/r with r ≠ q, choose an element of r outside q, possible because r and q are distinct maximal ideals. It annihilates B/r and becomes invertible after localization, so the localized factor is zero. If the factor is B/q, its localization is the residue field of B_q and is simple. Delete the repeated adjacent terms in the localized chain. What remains is a composition series of B_q/bB_q with exactly c_q simple factors. Therefore length_{B_q}(B_q/bB_q) = c_q; the equality of composition-series length with module length is Module.length_compositionSeries in the pinned library.

12. In the DVR B_q write b = uτ^(m_q), where u is a unit, τ is a uniformizer, and m_q is its nonnegative normalized order from step 6. Thus bB_q = τ^(m_q)B_q. The filtration of B_q/τ^(m_q)B_q by powers of τ has m_q factors equal to the residue field: multiplication by τ^j identifies B_q/(τ) with (τ^j)/(τ^(j+1)), using cancellation to check the kernel. Each factor is simple, so this quotient has length m_q. Combining with step 11 yields c_q = m_q.

13. Substitute c_q = m_q into step 9 and cast the finite natural-number equality to ℤ. Reindex Q by the bijection in step 3. Place.mem_fiberOver identifies the target index set with exactly v.fiberOver L. Steps 6 and 12 identify each term f_q m_q with (w.inertiaDeg E : ℤ) times w.ord of the image of b. Consequently the stated finite sum equals (n : ℤ), as required.

## Key steps

1. Establish the finite free Dedekind normalization and identify its maximal ideals with the finite place fiber.
2. Identify residue quotients with project residue fields using the canonical restriction algebra.
3. Choose a B-composition series using the assumed finite A-length.
4. Compute each simple factor's A-length as its residue degree.
5. Localize the series to recover each maximal ideal's multiplicity.
6. Compute the local quotient length from a uniformizer-power filtration.
7. Cast to integers and reindex by the project place fiber.

## Reference use

### local-project

Queries:
- `/runtime/bin/rg -n 'fiberEquiv|inertiaDeg|integralClosureAt|ord_norm|norm_ord' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/runtime/bin/rg -n 'norm.*length|length.*norm|det.*length|length.*det' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory`
- `/runtime/bin/rg -n 'length|span|pow|finrank' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `sed -n '120,230p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `sed -n '115,185p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Norm/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/name-collision-check.json`

The pinned project already supplies integralClosureAt, finite fibers, fiberEquiv, normalized uniformizer orders, and the canonical restriction residue algebra defining inertiaDeg. Mathlib supplies finite free normalization, localization DVRs, length additivity, and scalar-restriction length formulas. No determinant-length or norm-length theorem matched the RingTheory search. Project HEAD and all nine clean dependencies match their recorded revisions; inspected library files and the three project interface files match the snapshot byte-for-byte. The proposed names have no recorded DAG collision. All three proposed types and the residue-algebra, tower-map, and quotient scalar-action checks pass under the inherited isolated import-only Submission shim. Audited imported lemmas use only propext, Classical.choice, and Quot.sound. However, the unchanged authoritative Submission still fails on three pre-existing unavailable attribute targets. Actual Submission import validation remains an activation gate; neither comparator acceptance nor successful authoritative import is claimed.
