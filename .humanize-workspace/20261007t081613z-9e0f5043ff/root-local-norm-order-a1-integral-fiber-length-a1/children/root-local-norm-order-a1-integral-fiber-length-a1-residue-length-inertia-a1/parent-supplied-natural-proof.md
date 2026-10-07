# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.integral_fiber_length-a1`
- Child DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.residue_length_inertia-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the hypotheses. Use hw to replace v by w.restrict E; this makes the downstairs residue field literally the one used in inertiaDeg. Write A = v.toValuationSubring, m = maximalIdeal A, k = A/m, B = Place.integralClosureAt L v and q = (Place.fiberCenter L v hw).asIdeal. The pinned integral-closure instances in Def_AlgebraicCurve_PlacesOverDVR.lean make B a Dedekind domain, finite as an A-module, with fraction field L. Their hypotheses hold because A is a DVR and L/E is finite separable.

2. The ideal q is a nonzero prime, hence maximal in B. Place.fiberCenter_liesOver states that its contraction to A is m. Therefore S = B/q is a field whose A-action factors through k. This defines the k-algebra structure by sending the class of a ∈ A to its class in B/q. Choose a finite A-generating set of B. Its images generate S over k, because coefficients in A can be reduced modulo m. Thus S is a finite-dimensional k-vector space.

3. Put R = B_q. The homomorphism R → S sending a/s to the class of a divided by the class of s is well-defined. Allowed denominators lie outside q and so have nonzero images in S; equality of fractions implies equality after reduction and division in S. It is surjective because every class of a is the image of a/1. Its kernel consists of fractions with numerator in q, namely qR. Since qR is the maximal ideal of R, this induces a field isomorphism R/qR ≃ S.

4. Place.toValuationSubring_eq_of_restrict_eq identifies O_w with the embedded localization of B at q. The localization instance in DedekindDomain/AdicValuation.lean and IsLocalization.algEquiv identify R with O_w by an isomorphism commuting with the map from B. Consequently the inverse of the residue isomorphism in step 3 gives a field isomorphism e : S ≃ w.ResidueField. For a ∈ B, e sends its class to the residue of its image in O_w.

5. Verify the scalar action, not merely the abstract field isomorphism. For a ∈ A, its image in O_w is restrictInclusion E w a: both have underlying value algebraMap E L (a : E). Thus e sends the image of a in S to residue(restrictInclusion E w a). By Place.restrictResidueMap_residue this equals restrictResidueMap E w (residue a), and by Place.algebraMap_residueField_eq this is the canonical image of residue a in w.ResidueField. Since A → k is surjective, this verifies compatibility on every scalar of k. Hence e is k-linear for exactly the algebra defining w.inertiaDeg E. It follows that dim_k S = w.inertiaDeg E; finiteness of the dimension on the right also follows from this equivalence.

6. An additive subgroup of S is stable under A precisely when it is stable under k, because the A-action factors through the surjection A → k. Its A-submodule lattice is therefore its k-vector-subspace lattice. If d = dim_k S, any strict flag has at most d steps, since dimension strictly increases at each step. A basis gives a flag with exactly d steps. Therefore length_A(S) = (d : ℕ∞). Substitute the dimension identity from step 5 to obtain the required equality.

## Key steps

1. Replace v by w.restrict E and use the finite Dedekind normalization instances.
2. Use fiberCenter_liesOver to give B/q its residue-field scalar action and prove finite dimension.
3. Identify B/q with the residue field of B_q by reducing localized fractions.
4. Transport through the canonical localization identification with O_w.
5. Check compatibility with restrictResidueMap on residue representatives.
6. Compute A-module length from the finite-dimensional residue-field subspace lattice.

## Reference use

### local-project

Queries:
- `rg -n 'integralClosureAt|fiberEquiv|toValuationSubring_eq_of_restrict_eq|restrictResidueMap|inertiaDeg|finite_setOf_restrict_eq' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve*`
- `rg -n 'length_compositionSeries|length_eq_add_of_exact|length.*quotient|isDiscreteValuationRing_of_dedekind_domain' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory`
- `rg -n 'length.*(sum|localiz)|sum.*length|length.*finrank' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Localization .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `rg -n 'def algEquiv|def ringEquiv|theorem.*injective' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Localization/Basic.lean`
- `rg -n 'p06_9e0f5043ff_ifl_weighted_local_lengths|p06_9e0f5043ff_ifl_residue_length_inertia|p06_9e0f5043ff_ifl_local_length_order' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json Submission.lean Definitions Fermat`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Localization/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1/decomposition-typecheck/Submission.frozen-source-check.log`

The snapshot supplies finite Dedekind normalization, fiberEquiv, fiberCenter_liesOver, finite fibers, the localization description of place rings, canonical restriction residue maps, normalized uniformizer orders, composition-series length, and DVR quotient lengths. The targeted weighted-localization-length search returned no matches. Project revision 956e8c600d8b95b46948ae5e37b13930b5f3d06b and all nine clean pinned dependencies match their recorded revisions, including mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Checked source files match the snapshot. No proposed-name collisions were found. All three final types, quotient scalar-action checks, canonical residue-algebra checks, and localization-instance checks pass in the existing isolated import-only Submission interface. Audited library declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. The unchanged authoritative Submission still fails on three inherited unavailable attribute targets; authoritative import validation remains required before child proof work begins. No comparator acceptance is claimed.
