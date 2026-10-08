# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1`
- Child DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.residue_composition_series-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put C = B/bB. Restricting a B-submodule of C to A leaves its underlying subset unchanged. Thus this restriction preserves strict inclusions. Every finite strict chain of B-submodules therefore gives a strict chain of A-submodules of the same length. Since length_A(C) = n, the definition of module length as the dimension of the submodule lattice bounds every such chain length by n.

2. The set of lengths of finite strict chains of B-submodules is nonempty, because a chain with one term has length zero. It is contained in {0,…,n}, so it has a largest member. Choose a chain attaining this maximum. Its first term is zero: otherwise zero could be prepended, increasing its length. Its last term is C by the analogous argument of appending C. No submodule lies strictly between successive terms, since inserting one would contradict maximality. Hence this chain is a composition series s from zero to C. This argument also covers C = 0, when the one-term chain is a length-zero composition series.

3. Fix an index i and write N = s(i), N′ = s(i+1), and S = N′/N, where N is identified with its image under the inclusion into N′. The strict inclusion N < N′ makes S nonzero. A nonzero proper B-submodule of S would have a preimage strictly between N and N′ under the quotient map. The covering property of the series excludes this, so S is simple.

4. Choose u ≠ 0 in S. The B-linear map f : B → S given by f(a) = a·u has nonzero image, since f(1) = u. Simplicity makes its image all of S. Let r be its kernel, viewed as an ideal of B. The first isomorphism theorem gives B/r ≃ₗ[B] S, and r is proper because u ≠ 0. An ideal J strictly between r and B would yield a nonzero proper submodule J/r of B/r, hence of S. Thus r is maximal and consequently prime.

5. Multiplication by b annihilates C, because b times any residue class lies in bB. It therefore annihilates N′ and its quotient S. In particular f(b) = b·u = 0, so b ∈ r. Since b ≠ 0, r is not the zero ideal. The nonzero prime ideal r defines a point p(i) of HeightOneSpectrum B. Taking the inverse of the isomorphism in step 4 gives S ≃ₗ[B] B/p(i).asIdeal.

6. Choose these points and isomorphisms for all i in the finite index set Fin(s.length). The submodule of N′ used in forming S is exactly the preimage of N under the subtype map N′ → C, namely (s i.castSucc).comap (s i.succ).subtype. Thus the constructed data have precisely the asserted quotient types. If the index set is empty, its unique labeling function satisfies the factor condition vacuously. Together with the endpoints established in step 2, these data prove the conclusion.

## Key steps

1. Restriction of scalars bounds B-submodule chain lengths by the finite A-length.
2. A chain of maximal length has both endpoints and only covering steps.
3. Each successive quotient is simple.
4. A nonzero generator identifies each simple factor with a maximal-ideal quotient.
5. The annihilating nonzero element b makes each maximal ideal nonzero.
6. Choose the height-one labels and the required factor isomorphisms.

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
