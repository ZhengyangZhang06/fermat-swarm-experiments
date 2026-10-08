# Noncentral cancellation: Round 0 candidate record

This implementation-only round retains the existing candidate for
`Submission.p04_pb_60221840b0_noncentral_cancellation` (tracked node issue #167).
It adds no Lean declarations and changes no proof, dependency, frozen problem,
accepted handoff, comparator, or DAG. The requested read-only simplifier
recommended keeping the proof unchanged.

## Contract and integrity

The authoritative child has no approved dependencies. Its full Lean type in
the current plan matches the immutable dispatch `node.json`. Its accepted
six-step natural proof matches the immutable handoff byte-for-byte. The
dispatch is `2c918689a1e0fce536be435ba45b1510a9d01410`.

The entire `Submission.lean` diff from dispatch was inspected. It declares only
the selected theorem; `eval`, `before`, `after`, and `reindex` are local proof
steps. No placeholder, new axiom, unsafe mechanism, or new global helper is
present. The original root remains unchanged in its protected Fermat file.
The dependency configuration and tracked handoff are unchanged from dispatch.
`git diff --check` passes.

All nine installed packages match their `lake-manifest.json` revisions and have
clean tracked sources. The three reused upstream files listed below match the
pinned snapshot byte-for-byte. The candidate source SHA-256 is
`c54d318b7ff4ae1be82b8513d0d1ec5c1a6607c3e2401b5447878e919628de57`.

## Verification boundary

The installed Lean 4.33.1 toolchain passed both checks with exit zero:

- `lake env lean -DwarningAsError=true Submission.lean` produced no diagnostics.
- A temporary copy of the candidate with a `#check` ascription to the complete
  immutable child type and `#print axioms` passed with warnings fatal. The
  theorem's transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`.
  Both reused insertion lemmas use only `propext`; `Finset.sum_bij` and
  `MonoidAlgebra.single_neg` use the same three standard axioms as the candidate.

The executable used was
`/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake`.
The temporary audit is in the ignored round directory and introduces no tracked
helper declaration. These checks do not establish comparator acceptance.

Only the configured exact selected-node comparator is to be run on the resulting
clean commit. Its actual outcome belongs in the ignored round summary, preserving
the checked SHA. Previous challenge-import failures are not proof acceptance.
The independent reviewer rerun, publication, and DAG transition remain outer
controller responsibilities.

## Reference use

`reference_use` contains exactly one entry:

- source: `local-project`
  snapshot: `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8`
  manifest: `manifest.json` under that snapshot pins project
  `2475a3790d7ba0c3b10be8086001b154a45be597` and mathlib
  `db584cd6d46c92f209a44c0f1c829460d327499d`.
  Findings (paths relative to this exact snapshot):
  - Query `insertNth_apply_(below|above)|insertNth_comp_succAbove|removeNth_insertNth`
    in `mathlib/Mathlib/Data/Fin/Tuple/Basic.lean` found the insertion lemmas.
    Inspected lines 880–950; lines 931 and 936 supply the coordinate evaluation
    infrastructure reused by the candidate.
  - Query `sum_bij|sum_neg_distrib|sum_prod_type` in
    `mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean` found the additive
    reindexing declaration generated from `prod_bij`; inspected lines 445–478.
    Its membership, injectivity, surjectivity, and summand-equality obligations
    match the existing proof's use.
  - Query `single_neg` in `mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean`
    found line 910; inspected lines 902–915. It supplies coefficient negation.
  - Query `prism|prism_boundary|prismBoundary|noncentral_cancellation` in
    `project`, `mathlib/Mathlib/RepresentationTheory`, and
    `mathlib/Mathlib/AlgebraicTopology` returned no matches (rg exit 1).
  These are pinned upstream declarations, not new helper nodes.

## BitLesson Delta

Action: none
Lesson ID(s): NONE
Notes: The lesson file contains no entries; it was read before each mainline task.
