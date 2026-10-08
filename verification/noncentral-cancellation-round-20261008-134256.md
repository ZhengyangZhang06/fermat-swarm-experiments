# Noncentral cancellation: implementation revalidation

This record accompanies nested RLCR round `2026-10-08_13-42-56`. The sole tracked
declaration is `Submission.p04_pb_60221840b0_noncentral_cancellation` (issue #167).
Independent reviewer acceptance, wiki publication, and the DAG transition remain
outer-controller responsibilities.

## Candidate scope

The round started at `17b35880a8d1502cf42b9a3b22f658d1fb70a13b`. The complete proof
already exists in `Submission.lean`, introduced at `f52f3d895d67d77e510c037e55854fb08cf341ad`
and documented at `5d35a4405e1bcc47454399defe64dc727e3ca4ca`. It remains the candidate
being checked; it is not being imported as an approved dependency. This round
retains its source without adding another theorem or reopening decomposition.

`Submission.lean` SHA-256:
`c54d318b7ff4ae1be82b8513d0d1ec5c1a6607c3e2401b5447878e919628de57`.

The accepted parent-supplied proof is byte-identical to the committed handoff in
`.humanize-workspace/20261007t080920z-a816f3fa20/root-tate-index-annihilation-a1-cohomology-transfer-a1-restricted-sta-60221840b0/children/root-tate-index-annihilation-a1-cohomology-transfer-a1-restricted-sta-606bdf62ce/parent-supplied-natural-proof.md`.
The round plan's frozen type is identical to that child's `node.json`
`lean_statement`; `depends_on` is empty.

## Source and dependency integrity

- The complete diff from dispatch commit `2c918689a1e0fce536be435ba45b1510a9d01410`
  was inspected. The inherited Lean change places the selected atomic child in
  the designated `Submission.lean`; the protected root specification remains
  unchanged. The other inherited change is a verification document.
- The source declares exactly one theorem. `eval`, `before`, `after`, and
  `reindex` are local proof steps. No placeholders, new axioms, unsafe declarations,
  evaluator shortcuts, or additional global helper declarations were found.
- The protected root source SHA-256 remains
  `42953c937798c4a4ff8c5a5266936d11cb7f7836ede7175b49e6d157bd9e9551`.
- All nine installed Git dependencies match `lake-manifest.json` and have clean
  tracked sources. The project pin is `2475a3790d7ba0c3b10be8086001b154a45be597`;
  mathlib is `db584cd6d46c92f209a44c0f1c829460d327499d`; Lean is 4.33.1.
- `git diff --check 2c918689a1e0fce536be435ba45b1510a9d01410` passes.

## Local verification

`lake env lean -DwarningAsError=true Submission.lean` exited zero with no output,
using the installed Lean 4.33.1 toolchain. A temporary file containing the same
source, a `#check` against the complete frozen type, and `#print axioms` also
compiled with warnings fatal and exit zero. The transitive axiom list is exactly
`[propext, Classical.choice, Quot.sound]`.

The exact configured node comparator must still accept the committed candidate.
Its result will be recorded in the round summary after this evidence is committed,
so the comparator checks a stable, clean SHA. Earlier comparator failures remain
historical evidence. These local checks do not assert comparator acceptance.

## Reference use

`reference_use` contains exactly one source: **local-project**.

Snapshot:
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8`.

- Read `manifest.json`, which supplies the project and mathlib pins above.
- Query `prism|prism_boundary|prismBoundary|p04_pb_60221840b0_noncentral_cancellation`
  found no matches under `project/Definitions`, `mathlib/Mathlib/RepresentationTheory`,
  or `mathlib/Mathlib/AlgebraicTopology`.
- Query `insertNth_apply_below|insertNth_apply_above|insertNth_apply_same|insertNth_comp_succAbove`
  located the insertion lemmas in `mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`.
  Inspected lines 835–945; the candidate uses the below/above evaluation lemmas
  and insertion simplification supplied there.
- Query `sum_bij|sum_prod_type|sum_neg_distrib` under the big-operator files
  located `Finset.sum_bij`'s generated additive declaration in
  `mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`; inspected lines
  443–474. It reindexes by a membership-preserving injective and surjective map,
  with equality of summands, as used by the candidate.
- Both inspected mathlib files match the installed pinned sources byte-for-byte.
  These are upstream library declarations, not newly introduced helpers.

## BitLesson Delta

Action: none
Lesson ID(s): NONE
Notes: The lesson file contains no entries. It was reread for each task; no lesson
was added or changed.
