# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.integral_fiber_length-a1`
- Child DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix A, B, b, n and the stated length equality, and put C = B/bB. Every B-submodule of C is an A-submodule under restriction of scalars. This restriction preserves and reflects strict inclusion because it leaves the underlying subsets unchanged. Consequently every finite strict chain of B-submodules has at most n steps.

2. The possible lengths of such chains form a nonempty subset of {0,…,n}; choose a chain of maximum length. Its first term is zero and its last term is C, since otherwise an endpoint could be added. Each successive quotient is simple: a nonzero proper submodule of that quotient would lift to an additional term in the chain. Thus C has a finite B-composition series. If C is zero, take its length-zero series.

3. For a simple factor S, choose s ≠ 0 in S. The map B → S sending a to as is surjective because its image is a nonzero submodule. Its kernel r is a proper ideal, and any ideal strictly between r and B would give a nonzero proper submodule of S. Hence r is maximal and S is B-linearly isomorphic to B/r. Multiplication by b is zero on C and therefore on every subquotient S. Thus b ∈ r. Since b ≠ 0, r is nonzero and defines a point of HeightOneSpectrum B. The ideal r is uniquely determined by S: the annihilator of B/r is exactly r, as follows by applying an annihilating element to the class of 1.

4. For each height-one prime q, let c_q be the number of factors with annihilator q.asIdeal, and let λ_q = length_A(B/q.asIdeal). Restricting the factor isomorphisms to A and applying Module.length_eq_add_of_exact to each step of the composition series gives length_A(C) = Σ_q (c_q : ℕ∞)λ_q. This is a finite regrouping because both the series and the indexing spectrum are finite. No assumption that every λ_q is finite is needed: terms with c_q = 0 are zero in ℕ∞.

5. Fix q and localize at T = B \ q.asIdeal. Localization preserves the exact sequences in the series. Explicitly, if x/s maps to zero, some t ∈ T kills the image of x; hence tx belongs to the original kernel. An original preimage of tx, divided by ts, gives a localized preimage of x/s. The same zero-fraction criterion proves that an injective map remains injective, and lifting numerators proves preservation of surjectivity. Applied to B → C, it identifies the localized C with R_q/bR_q: a fraction a/s maps to zero exactly when some t ∈ T satisfies ta ∈ bB, which is equivalent to a/s belonging to bR_q.

6. Consider a factor B/r. If r ≠ q.asIdeal, both ideals are maximal because they are nonzero primes of a Dedekind domain. Thus some t ∈ r lies outside q.asIdeal. It annihilates B/r and becomes invertible after localization, so the localized factor is zero. If r = q.asIdeal, localization leaves the field B/q unchanged: send a fraction to its numerator class divided by its denominator class. The denominator class is nonzero. This identifies the localized factor with the residue field of R_q, hence with a simple R_q-module.

7. The localized chain is a chain of submodules of R_q/bR_q by exactness. Delete repeated adjacent terms. Its remaining successive quotients are precisely the c_q nonzero localized factors, all simple. It is therefore a composition series of length c_q, including the length-zero case. Module.length_compositionSeries gives length_{R_q}(R_q/bR_q) = (c_q : ℕ∞).

8. Substitute these local lengths into the equality in step 4, commute the two factors in each product, and use length_A(C) = (n : ℕ∞). The resulting equality is exactly the asserted finite sum.

## Key steps

1. Bound B-submodule chains by the assumed finite A-length and obtain a B-composition series.
2. Classify each simple factor as B/r; its annihilator contains the nonzero element b, so r is a height-one prime.
3. Use A-length additivity to express the total length through factor multiplicities.
4. Localize the series exactly and identify the localized quotient with R_q/bR_q.
5. Show that localization kills factors at other maximal ideals and preserves exactly the q-factors.
6. Identify each local length with its multiplicity and substitute into the finite sum.

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
