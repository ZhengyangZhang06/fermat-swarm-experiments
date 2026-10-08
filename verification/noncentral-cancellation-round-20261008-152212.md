# Noncentral cancellation: Round 0 verification record

Round: `2026-10-08_15-22-12`. Starting revision:
`ffe2f57096e9e2ad5c566ab10b1934fd845dc41d`.

The only tracked theorem is
`Submission.p04_pb_60221840b0_noncentral_cancellation` (existing node issue #167).
The candidate proof already existed at the start of this round, introduced in
`f52f3d895d67d77e510c037e55854fb08cf341ad`. It is retained as this node's candidate,
not imported as an accepted dependency. A read-only simplifier recommended no
changes. This round changes no Lean source, dependency, handoff, or verifier.

## Local validation

- Read the frozen problem and accepted six-step natural proof. The latter is
  byte-identical to the immutable dispatch handoff. The plan's exact Lean type
  matches the dispatch `node.json`; its dependency list is empty.
- The installed Lean 4.33.1 command `lake env lean -DwarningAsError=true
  Submission.lean` exited zero without diagnostics. The executable used was
  `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake`.
- A temporary audit containing the candidate source, a `#check` ascription to
  the entire immutable child type, and `#print axioms` exited zero with warnings
  fatal. The theorem's transitive axioms are exactly
  `[propext, Classical.choice, Quot.sound]`. The reused insertion lemmas use only
  `propext`; `Finset.sum_bij` and `MonoidAlgebra.single_neg` use the same three
  standard axioms as the candidate.
- All nine installed dependencies match `lake-manifest.json` and have clean
  tracked sources. Project pin: `2475a3790d7ba0c3b10be8086001b154a45be597`.
  Mathlib pin: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Inspected the complete Lean diff from dispatch
  `2c918689a1e0fce536be435ba45b1510a9d01410`; only the selected theorem is declared.
  `eval`, `before`, `after`, and `reindex` are local proof steps. No placeholders,
  extra global helper declarations, new axioms, or unsafe mechanisms occur.
  `git diff --check` passes.
- The protected root specification is byte-identical to the frozen project.
  Dependency configuration and the selected handoff are unchanged from dispatch.
- Candidate `Submission.lean` SHA-256:
  `c54d318b7ff4ae1be82b8513d0d1ec5c1a6607c3e2401b5447878e919628de57`.

These checks are not comparator acceptance. After this record is committed,
run only the configured selected-node comparator on the clean exact SHA.
Record its result in the ignored round summary to keep the checked SHA stable.
Earlier challenge-import failures remain historical evidence, not a substitute
for this round's comparator result. Independent reviewer comparison, publication,
and DAG acceptance belong to the outer controller.

## Reference use

`reference_use` has exactly one entry:

- source: `local-project`
  snapshot: `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8`
  manifest: `manifest.json` at that snapshot; pins listed above.
  findings:
  - Query `insertNth_apply_(below|above)|insertNth_comp_succAbove|removeNth_insertNth`
    found the insertion infrastructure in `mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`.
    Inspected lines 880–949; the below/above lemmas at lines 931 and 936 justify
    the coordinate evaluation in the candidate.
  - Query `sum_bij|sum_neg_distrib|sum_prod_type` located the additive declaration
    generated from `prod_bij` in
    `mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`.
    Inspected lines 445–474: membership, injectivity, surjectivity, and summand
    equality are the obligations used by the finite-sum reindexing.
  - Query `single_neg` located
    `mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean:910`.
    Inspected lines 902–914: coefficients negate additively, as used by cancellation.
  - Query `prism|prism_boundary|prismBoundary|noncentral_cancellation` returned
    no matches in `project`, `mathlib/Mathlib/RepresentationTheory`, and
    `mathlib/Mathlib/AlgebraicTopology` under the snapshot.
  - All three reused library files match the installed pinned mathlib files
    byte-for-byte. Their axiom checks are reported above. They are existing
    upstream declarations, not new helpers.

## BitLesson Delta

Action: none
Lesson ID(s): NONE
Notes: The lesson file contains no entries. It was read for the research,
implementation validation, build/audit, and commit/comparator tasks.
