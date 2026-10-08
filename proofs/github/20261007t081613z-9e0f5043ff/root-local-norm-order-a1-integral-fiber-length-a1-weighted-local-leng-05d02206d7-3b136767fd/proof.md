# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1`
- Child DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1.localized_series_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data and endpoint equalities. Put r = s.length, R = Localization T, and N_j = s(j) for 0 ≤ j ≤ r. For i < r, let Q_i = N_{i+1}/D_i, where D_i is the preimage of N_i under N_{i+1} → M. This is exactly the comap denominator in the statement. Since a composition series is increasing, inclusion defines an injective B-linear map f_i : N_i → N_{i+1}. The quotient map g_i : N_{i+1} → Q_i is surjective, and its kernel is precisely the image of f_i. Thus these maps form a short exact sequence.

2. For any B-linear map h : X → Y, its localized map sends x/u to h(x)/u. It is well-defined because applying h preserves the relation defining equality of fractions. It is additive by the fraction addition formula. It is R-linear because h(ax)/(vu) = a·h(x)/(vu), which compares its values on the canonical action (a/v)·(x/u).

3. Localization preserves injectivity, surjectivity, and exactness for the sequences in step 1. For injectivity, if f_i(x)/u = 0, the zero-fraction criterion gives t ∈ T with f_i(tx) = 0. Injectivity gives tx = 0, hence x/u = 0; an additive map with trivial kernel is injective. For surjectivity, lift the numerator of any fraction in the localized Q_i through g_i.

4. For exactness in the middle, suppose g_i(x)/u = 0. There is t ∈ T such that g_i(tx) = 0. Original exactness supplies y ∈ N_i with f_i(y) = tx. The localized image of y/(tu) is tx/(tu) = x/u. Conversely, every localized image of f_i maps to zero because g_i ∘ f_i = 0. Together with steps 2 and 3, this proves a short exact sequence of R-modules from LocalizedModule T N_i through LocalizedModule T N_{i+1} to LocalizedModule T Q_i.

5. Apply Module.length_eq_add_of_exact to each sequence. It gives length_R(LocalizedModule T N_{i+1}) = length_R(LocalizedModule T N_i) + length_R(LocalizedModule T Q_i). This library theorem applies to arbitrary module lengths in ℕ∞; no finite-length hypothesis is needed.

6. Since N_0 = 0, its localization is zero and has length zero. Induction on j using step 5 therefore gives length_R(LocalizedModule T N_j) = Σ_{i<j} length_R(LocalizedModule T Q_i) for every j ≤ r. The induction uses only addition and finite sums, with no subtraction or cancellation of potentially infinite lengths.

7. Since N_r = ⊤, its canonical identification with M localizes to an R-linear equivalence: send a fraction of a submodule element to the fraction of its underlying element, and use membership in ⊤ for the inverse. Length invariance under this equivalence turns the induction formula at j = r into the asserted sum indexed by Fin r. If r = 0, the endpoints imply M = 0, and the same argument gives zero equal to the empty sum.

## Key steps

1. Form the canonical short exact sequence for each successive quotient.
2. Construct localized maps and verify their canonical R-linearity.
3. Prove preservation of injectivity, surjectivity, and exactness using fractions.
4. Apply module-length additivity to each localized sequence.
5. Sum inductively from the zero endpoint without cancellation.
6. Identify the localized final endpoint with the localization of M, including the length-zero case.

## Reference use

### local-project

Queries:
- `length_compositionSeries|length.*[Ll]ocaliz|[Ll]ocaliz.*length|map_exact|localized.*[Qq]uotient|quotient.*[Ll]ocaliz`
- `length.*(sum|localiz)|sum.*length|localiz.*length`
- `HeightOneSpectrum|instance.*[Mm]aximal|theorem.*[Mm]aximal|lemma.*[Mm]aximal`
- `map_injective|map_surjective|linearEquiv|module.*ocalization|[Ll]inearMap.*extendScalars|def map|instance.*Module|mkLinearMap`
- `p06_9e0f5043ff_llm_localized_residue_factors|p06_9e0f5043ff_llm_localized_series_sum`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Module/LocalizedModule/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Module/LocalizedModule/Exact.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Module/LocalizedModule/Submodule.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Localization`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-04a817ef67/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-04a817ef67/decomposition-typecheck/ExactnessAxioms.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-04a817ef67/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-04a817ef67/decomposition-typecheck/Submission.frozen-source-check.log`

The snapshot supplies exact localization, preservation of injectivity and surjectivity, localizedQuotientEquiv, length additivity, simple-module length one, zero-module length zero, and maximality and extensionality of height-one primes. The targeted localization-length search in Localization and DedekindDomain found no matching formula. Project revision 956e8c600d8b95b46948ae5e37b13930b5f3d06b and all nine dependencies are clean and match their pins, including mathlib db584cd6d46c92f209a44c0f1c829460d327499d; inspected sources match the snapshot. Both proposed types elaborate after import Submission in the existing import-only interface. Explicit fraction-action checks confirm the canonical localized-module actions, including on successive quotients. Audited library declarations use only propext, Classical.choice, and Quot.sound. No proposed-name collision was found in the DAG, declarations, decompositions, or published handoffs. Authoritative import validation remains blocked: the unchanged frozen Submission source fails on three inherited unknown attribute targets. This must be resolved before child proof work begins; interface checking is not comparator acceptance.
