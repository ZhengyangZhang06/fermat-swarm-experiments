# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1`
- Child DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.length_sum_factors-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write m = s.length and N_j = s(j) for 0 ≤ j ≤ m. For each i < m, put Q_i = N_{i+1}/N_i, using the inclusion N_i → N_{i+1}. Its denominator is the preimage of N_i under the subtype map N_{i+1} → M, exactly the comap appearing in the statement. Choose a B-linear isomorphism e_i : Q_i ≃ B/p(i).asIdeal from the given nonempty type.

2. The inclusion N_i → N_{i+1} is injective. The quotient map N_{i+1} → Q_i is surjective and has kernel the image of that inclusion. These maps therefore form a short exact sequence. Restricting scalars to A changes neither their underlying functions nor their kernels and images, so the sequence remains exact over A.

3. The scalar-tower hypothesis identifies multiplication by a ∈ A with multiplication by algebraMap A B a on M, its submodules, and these quotients. The same identity holds for the canonical A-action on B/p(i).asIdeal. Consequently each B-linear e_i is also A-linear. Length invariance under this isomorphism and Module.length_eq_add_of_exact applied to step 2 give length_A(N_{i+1}) = length_A(N_i) + length_A(B/p(i).asIdeal).

4. Since N_0 = 0, its A-length is zero. Induction on j using the identity in step 3 gives length_A(N_j) = Σ_{i<j} length_A(B/p(i).asIdeal) for every j ≤ m. This induction uses only addition and finite sums in ℕ∞, without cancellation or any assumption that the summands are finite.

5. At j = m, the endpoint hypothesis N_m = M identifies the top submodule with M by its canonical A-linear equivalence. The induction formula is therefore exactly the asserted sum indexed by Fin m. When m = 0, both endpoints coincide, M is zero, and the same formula is the empty-sum equality.

## Key steps

1. Form the short exact sequence for each successive quotient.
2. Restrict its maps and factor isomorphisms to A using the scalar tower.
3. Apply length additivity to every step.
4. Inductively sum the identities from the zero endpoint.
5. Identify the final endpoint with M, including the empty-series case.

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
