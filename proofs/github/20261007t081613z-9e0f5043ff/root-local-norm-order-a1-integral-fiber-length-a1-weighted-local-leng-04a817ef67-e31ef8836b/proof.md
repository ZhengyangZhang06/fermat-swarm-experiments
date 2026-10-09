# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1`
- Child DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix q, let T = B \ q.asIdeal, and put R = T⁻¹B. Localization at T preserves short exact sequences. Indeed, for an exact sequence with maps f and g, if g(x)/s = 0, the zero-fraction criterion supplies t ∈ T with g(tx) = 0. Exactness supplies y with f(y) = tx, and then y/(ts) maps to x/s. This proves exactness in the middle; the reverse inclusion follows from g ∘ f = 0. If f is injective and f(x)/s = 0, some t ∈ T satisfies f(tx) = 0, hence tx = 0 and x/s = 0. Surjectivity after localization follows by lifting each numerator. These arguments also show that the induced maps are R-linear.

2. The quotient map B → C induces a surjective R-linear map R → T⁻¹C taking a/s to the fraction of the class of a. Its kernel consists of those a/s for which some t ∈ T satisfies ta ∈ bB. If ta = bd, then a/s = image(b)·(d/(ts)), so this fraction lies in image(b)R. Conversely every multiple of image(b) maps to zero because b annihilates C. Thus the kernel is precisely image(b)R, and the quotient map induces an R-linear isomorphism R/image(b)R ≃ T⁻¹C.

3. Write N_j for the terms of s and Q_i = N_{i+1}/N_i for its successive quotients. Applying step 1 to their short exact sequences and to the injections N_j → C identifies T⁻¹N_j with an increasing chain of R-submodules of T⁻¹C. This chain starts at zero and ends at T⁻¹C. Its successive quotient at i is R-linearly isomorphic to T⁻¹Q_i, and the supplied factor isomorphism identifies this with T⁻¹(B/p(i).asIdeal).

4. Suppose p(i) ≠ q, and set r = p(i).asIdeal. Height-one primes of a Dedekind domain are maximal, and equality of their underlying ideals implies equality of the points. Thus r and q.asIdeal are distinct maximal ideals. There exists t ∈ r outside q.asIdeal: otherwise r would be contained in q.asIdeal, forcing equality by maximality. This t annihilates B/r and becomes a unit in R. Therefore every element of T⁻¹(B/r) is zero, because multiplying it by t gives zero and multiplication by t is invertible.

5. Suppose p(i) = q. The quotient k = B/q.asIdeal is a field. Every denominator t ∈ T has a nonzero, hence invertible, class in k. The map T⁻¹k → k sending u/t to u·(t mod q)⁻¹ is well-defined: equality of fractions becomes equality after multiplying by a class from T, which is invertible in k. Its inverse is u ↦ u/1. Give k the R-action in which a/s acts by multiplication by (a mod q)/(s mod q); the two maps are R-linear inverses. Any R-submodule of k is in particular a B-submodule, and B → k is surjective, so it is an ideal of the field k. Hence k is a nonzero simple R-module. Thus precisely the indices with p(i) = q give nonzero localized successive quotients, and each such quotient is simple.

6. Let c be the cardinality of the finite subtype {i : Fin(s.length) | p(i) = q}. By steps 3–5, the localized chain has equal adjacent terms exactly at the indices not counted by c. Delete these repetitions. Every retained transition corresponds to one of the c nonzero successive quotients: intervening deleted terms are equal submodules, so deleting them does not change that transition’s quotient. The resulting chain therefore has exactly c strict steps, all with simple successive quotients, and retains the endpoints zero and T⁻¹C. It is a composition series of length c. If c = 0, all terms of the localized chain coincide, so T⁻¹C = 0 and the resulting series has length zero.

7. Module.length_compositionSeries gives length_R(T⁻¹C) = (c : ℕ∞). Transfer this equality along the R-linear isomorphism in step 2. Since c is Nat.card of the finite subtype in the statement and R is the specified localization at q, the transferred equality is exactly the required local quotient length formula.

## Key steps

1. Prove exactness, injectivity preservation, and surjectivity preservation for localization by fractions.
2. Identify the localized principal quotient with R_q/image(b)R_q by computing the kernel.
3. Localize the given series and its factor isomorphisms.
4. Kill factors belonging to other maximal ideals using an inverted annihilator.
5. Identify the q-factors with a simple residue-field module.
6. Delete repeated terms and count the remaining composition factors.
7. Apply composition-series length and transfer through the quotient isomorphism.

## Reference use

### local-project

Queries:
- `rg -n 'length_compositionSeries|length_eq_add_of_exact|hasPrincipalDivisors_of_transcendental|length.*localiz|localiz.*length' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`
- `rg -n 'length.*(sum|localiz)|sum.*length|localiz.*length' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Localization .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain`
- `rg -n 'isFiniteLength_iff_exists_compositionSeries|isFiniteLength_of_exists_compositionSeries' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/FiniteLength.lean`
- `rg -n 'p06_9e0f5043ff_wll_residue_composition_series|p06_9e0f5043ff_wll_length_sum_factors|p06_9e0f5043ff_wll_local_length_multiplicity' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json Submission.lean Definitions Fermat`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/FiniteLength.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/SimpleModule/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Module/LocalizedModule/Exact.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-lengths-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-lengths-a1/decomposition-typecheck/LocalizationAxioms.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-lengths-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-lengths-a1/decomposition-typecheck/provenance-check.json`

The snapshot supplies composition-series existence, classification of simple modules by maximal-ideal quotients, length additivity, exact localization, and maximality of height-one primes. The focused weighted-localization-length search returned no matches. Project revision 956e8c600d8b95b46948ae5e37b13930b5f3d06b and all nine clean pinned dependencies match their recorded revisions, including mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Inspected library sources match the snapshot. Audited declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. No proposed-name collisions were found. All three types and canonical quotient scalar-action checks pass after import Submission in the existing import-only interface. However, the unchanged authoritative Submission still fails on three inherited unknown attribute targets; authoritative import validation remains required before child proof work begins. No comparator acceptance is claimed.
