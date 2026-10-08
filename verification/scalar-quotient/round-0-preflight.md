# Scalar quotient Round 0 preflight

This audit records the 2026-10-08 nested implementation round before its fresh comparator request. It is not proof acceptance or a replacement for controller evidence.

## Candidate

The existing `Submission.p06_9e0f5043ff_dlen_scalar_quotient` is retained without edits. Relative to frozen source commit `956e8c600d8b95b46948ae5e37b13930b5f3d06b`, the Lean diff adds exactly this theorem in namespace `Submission`. Its binders, hypothesis and existential length/order conclusion agree textually with the selected-node contract. There are no new named helpers, axioms, unsafe constructs or placeholders. The original root declaration, its `sorry`, and all attribute commands remain unchanged.

The proof factors the scalar as a unit times a uniformizer power, rewrites its ideal to a power of the maximal ideal, uses the pinned quotient length theorem, and computes order with the existing normalized order law. A requested read-only simplifier review found no warranted simplification and made no edits. This is a source audit, not an independent mathematical acceptance review.

## Local validation

- Located Lean 4.33.1 at `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean`; its reported commit is `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Ran `lake env lean -DwarningAsError=true Submission.lean` with that toolchain prepended to PATH. Exit 1: unknown constants at lines 9–11, respectively `AlgebraicCurve.IsCurveOver.instNontrivialKaehler`, `AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply`, and `AlgebraicCurve.SemilinearAut.coe_torsion_smul`; line 14 reports the inherited root declaration uses `sorry`.
- Both snapshot repositories are clean and match the manifest: project `956e8c600d8b95b46948ae5e37b13930b5f3d06b`, mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
- All nine installed packages have clean Git status and HEAD equal to their exact `lake-manifest.json` revision.
- The three project imports `Def_AlgebraicCurve_DivisorClassGroup`, `Def_AlgebraicCurve_DivisorPushPull`, and `Def_AlgebraicCurve_PlacesOverDVR`, plus mathlib's `DiscreteValuationRing/Basic.lean`, match the pinned snapshot byte for byte.

The full-source build is blocked before this round can claim warning-clean verification. Only the specified selected-node comparator will be invoked. Transitive axiom acceptance, exact-contract kernel comparison, and independent reviewer acceptance remain unestablished until their configured gates succeed. Candidate-only edits cannot repair an independently prepared challenge with the same frozen import/attribute inconsistency.

## Reference use

Exactly one source: `local-project`.

Snapshot: `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`; manifest: `manifest.json` beneath that directory.

Queries and inspected files, relative to the snapshot:

- `rg -n 'ord_coe_unit|ord_coe_irreducible|ord_unit_smul_zpow|IsDiscreteValuationRing' project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`: the DVR instance is at line 73; normalized unit/irreducible order laws and the combined order formula are at lines 141–161. Read lines 60–170.
- `rg -n 'eq_unit_mul_pow_irreducible|exists_irreducible|maximalIdeal_eq|length_quotient_pow_maximalIdeal' mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`: factorization is at line 338, uniformizer existence at 105, maximal-ideal identification at 98, and quotient length at 555. Read lines 330–350 and 550–590.
- `rg -n 'length.*ord|ord.*length|dlen_scalar_quotient' project/Definitions mathlib/Mathlib/RingTheory/DiscreteValuationRing`: exit 1, no matches.

These are existing pinned library declarations, not new helper nodes. The source and dependency checks above establish local provenance compatibility; they do not replace the required transitive axiom/comparator checks.

## BitLesson Delta

Action: none

Lesson ID(s): NONE

Notes: Read `.humanize/bitlesson.md` before each task; it contains no lessons. No new lesson was added because no new repair was established.
