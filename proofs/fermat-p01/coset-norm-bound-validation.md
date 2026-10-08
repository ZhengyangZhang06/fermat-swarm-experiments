# Coset norm bound: author validation

Selected node: `root.gamma0_finite_dimensional-a1.coset_norm_bound-a1`.
Only tracked theorem: `Submission.f036cc6b1f_fd_norm_bound`.

## Current round: 2026-10-08 18:43:04 UTC

The latest requested repair remains constrained by the frozen context: the candidate's
selected theorem comes after the two failing attribute commands, while the inspected
local verifier independently copies the frozen proof base into its challenge and
exports that challenge first. No allowed edit of this selected theorem can repair
either earlier command. The exact statement, accepted prose, imports, dependencies,
and verifier remain unchanged; no dummy declarations or error suppression were added.

A fresh read-only simplifier review found no concrete defect or useful simplification
of the existing proof. The source/dependency audit again confirms nine clean pinned
package repositories, 81 identical snapshot Definitions files, 20 identical imported
project modules, and six identical inspected mathlib files. The complete source diff
from proof base `218176a9f57bf541cd6a4601fd809a5b3c5b91d2` introduces only
`Submission.f036cc6b1f_fd_norm_bound`; the inherited root `sorry` is untouched.

The fresh `rg` queries, source audit, simplifier review, warning-fatal scoped diagnostics,
and exact-node comparator outcome are recorded under
`.humanize/rlcr/2026-10-08_18-43-04/validation/` and in that round's summary.
The structured research record has exactly one `reference_use` entry, source
`local-project`. Searches for all 15 header targets in pinned Definitions/mathlib
and for `fd_norm_bound|norm_domination|coset_norm` have no matches; the two reported
names occur only in the pinned project's two frozen headers. The library provenance
below remains applicable and was inspected again this round.

This evidence update does not claim that the header was repaired or that the outer
reviewer has accepted the proof. The required clean-commit comparator will be recorded
separately from the local diagnostics; a passing comparator must not conceal a failed
full-context build. BitLesson selection remains `NONE` (the catalogue is empty).

The fresh Lean 4.33.1 warning-fatal diagnostics have now completed: the selected body
and literal frozen-type example exit 0, and the version retaining the frozen attributes
exits 1 on the same two unknown constants. All four scoped transitive axiom reports
(selected theorem, norm, integral-slash decay, Gamma0 finite index) contain only
`propext`, `Classical.choice`, and `Quot.sound`. These diagnostics omit the unrelated
root theorem and do not replace the configured comparator.

## Previous round: 2026-10-08 18:03:37 UTC
## Current round: 2026-10-08 18:03:37 UTC

The selected Lean proof and its complete frozen prefix remain unchanged. A fresh
read-only simplifier review found no concrete proof defect or worthwhile simplification.
This round adds evidence only; it does not claim proof acceptance or a source repair.

The blocker is independent of the candidate proof. Inspection of the configured
`/runtime/flows/math-lean-flow/scripts/verify-frozen-node.py` shows that `verify()`
copies proof base `218176a9f57bf541cd6a4601fd809a5b3c5b91d2` into the challenge,
then gives the child challenge `import Submission`. `compare()` exports that
challenge before exporting the solution. Thus no edit confined to the selected
candidate declaration can repair the missing constants in the challenge's frozen
header. Altering the frozen base, imports, header, dependencies, or verifier is
outside this implementation contract. No such change was made.

Fresh source checks confirm all nine dependency repositories are clean at their
manifest revisions. All 81 snapshot Definitions files, all 20 transitively imported
project modules, and the six cited mathlib files match the pinned snapshot exactly.
An exact-name rg search for all 15 attribute targets in snapshot `project/Definitions`
and `mathlib/Mathlib` returns no matches. Searching the entire snapshot `project/`
for the two reported names finds only the two frozen attribute-command headers.
`fd_norm_bound|norm_domination|coset_norm` has no matches in snapshot Definitions
or mathlib's modular-form directory. These textual results are evidence of the
source mismatch, not a substitute for Lean's environment check.

Fresh evidence is stored in
`.humanize/rlcr/2026-10-08_18-03-37/validation/`: source/dependency audit, complete
candidate diff, protected-artifact digests, reference-search logs, one structured
`reference_use` entry with source `local-project`, and the simplifier review.
Fresh Lean 4.33.1 diagnostics with `-DwarningAsError=true` and the project options
give exit 0 for the unchanged selected proof plus literal frozen-type check, with
only `propext`, `Classical.choice`, and `Quot.sound` in all four axiom reports.
Retaining the frozen header gives exit 1 on the same two unknown constants at
lines 9–10. Both diagnostics exclude the unrelated root theorem. The exact
clean-SHA comparator result is recorded in this round's summary after the commit
and run; these diagnostic results do not establish acceptance. The older checks
below are historical.

The existing implementation in `Submission.lean` is retained unchanged. It realizes the
accepted parent proof: the finite coset factors tend to zero, so they are simultaneously
bounded by one above a common height; separating the identity factor yields the bound
with `C = 1`. The requested simplifier review found no justified change.

The exact type remains:

```lean
∀ (M : ℕ) [NeZero M] (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2), ∃ C Y : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, Y ≤ z.im → ‖ModularForm.norm (MonoidHom.range (Matrix.SpecialLinearGroup.mapGL ℝ : Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℝ)) f z‖ ≤ C * ‖f z‖
```

## Fresh author checks, 2026-10-08, round started 16:35:33 UTC

- Lean 4.33.1 (commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), `-DwarningAsError=true` and the project Lean options: the unchanged selected theorem in a fresh diagnostic importing
## Fresh author checks, 2026-10-07
## Fresh author checks, 2026-10-07, round started 20:19:24 UTC
## Fresh author checks, 2026-10-07, round started 21:39:42 UTC
## Fresh author checks, 2026-10-07, round started 23:12:00 UTC
## Fresh author checks, 2026-10-08, round started 06:03:43 UTC
## Fresh author checks, 2026-10-08, round started 11:57:32 UTC
## Fresh author checks, 2026-10-08, round started 12:54:01 UTC
## Fresh author checks, 2026-10-08, round started 14:05:24 UTC
## Fresh author checks, 2026-10-08, round started 15:32:30 UTC

- Lean 4.33.1 (commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), `-DwarningAsError=true` and the project Lean options: the unchanged selected theorem in a fresh diagnostic importing
  `Definitions.Def_ModularForm_HeckeOperatorForms` passes, including an anonymous check
  against the literal frozen type.
- Transitive axiom reports for the selected theorem, `ModularForm.norm`,
  `CuspFormClass.zero_at_infty_slash`, and `CongruenceSubgroup.instFiniteIndexGamma0`
  contain only `propext`, `Classical.choice`, and `Quot.sound`.
- All nine dependency repositories have clean status and their manifest-pinned HEADs.
- Six inspected mathlib files and all 81 snapshot project Definitions files match the
  local reference snapshot byte-for-byte.
- The complete inherited source diff preserves the frozen Submission prefix. Its only
  new theorem is the selected declaration, with no local placeholders, new axioms,
  unsafe mechanisms, or weakened statement. The complete diff against this node's proof base
  `218176a9f57bf541cd6a4601fd809a5b3c5b91d2` contains only the selected proof,
  a runtime skill ignore rule in `.gitignore`, and this validation report.
  This round changes only the report; local round records remain ignored.

**Required validation remains blocked.** The fresh diagnostic retaining the frozen imports
and attribute commands, while excluding the unrelated root theorem, exits 1. The two
grouped commands fail before this node's proof. A fresh exact-name source search across
snapshot `project/Definitions` and `mathlib/Mathlib` returns no matches for their 15 targets.
That textual search alone does not rule out generated declarations; the Lean errors
establish the missing targets in the actual imported environment.
The first errors name
`FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions`
and `FreyPackage.ModMCarrier.coe_rescaleLin_apply`. The fresh selected-body diagnostic exits zero;
the fresh full-context diagnostic exits one. Thus the passing diagnostic without
the attribute commands is not full-context acceptance. Both fresh diagnostics exclude the
unrelated root theorem; no root or sibling theorem was validated and no root comparator was run.

The inherited implementation and historical comparator reports were not treated as
proof acceptance. All diagnostics above were rerun in this round. No prior process,
request, or controller state was restarted, canceled, or modified.
- Five inspected mathlib files and all 81 snapshot project Definitions files match the
  local reference snapshot byte-for-byte.
- The complete inherited source diff preserves the frozen Submission prefix. Its only
  new theorem is the selected declaration, with no local placeholders, new axioms,
  unsafe mechanisms, or weakened statement. The complete diff against this node's proof base
  `218176a9f57bf541cd6a4601fd809a5b3c5b91d2` contains only the selected proof,
  a runtime skill ignore rule in `.gitignore`, and this validation report.
  This round changes only the report; local round records remain ignored.

**Required validation remains blocked.** The fresh diagnostic retaining the frozen imports
and attribute commands, while excluding the unrelated root theorem, exits 1. The two
grouped commands fail before this node's proof. A fresh exact-name source search across
snapshot `project/Definitions` and `mathlib/Mathlib` returns no matches for their 15 targets.
That textual search alone does not rule out generated declarations; the Lean errors
establish the missing targets in the actual imported environment.
The first errors name
`FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions`
and `FreyPackage.ModMCarrier.coe_rescaleLin_apply`. The fresh selected-body diagnostic exits zero;
the fresh full-context diagnostic exits one. Thus the passing diagnostic without
the attribute commands is not full-context acceptance. Both fresh diagnostics exclude the
unrelated root theorem; no root or sibling theorem was validated and no root comparator was run.

The inherited implementation and historical comparator reports were not treated as
proof acceptance. All diagnostics above were rerun in this round. No prior process,
request, or controller state was restarted, canceled, or modified.

The current plan requires a fresh exact-node comparator run on a clean committed
candidate. Its result belongs to that exact SHA and is recorded in the local round
summary after the run; this pre-comparison report makes no comparator acceptance claim.
Independent reviewer acceptance, wiki publication, and DAG transition remain controller
tasks. The frozen context, dependencies, accepted prose, and controller state are unchanged.

## Local reference provenance

The sole source is `local-project`, snapshot
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb`.
Its manifest pins project `61b5f85556ac71631ccad822e0694511234f7132` and mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

Under that snapshot, `mathlib/Mathlib/NumberTheory/ModularForms/NormTrace.lean:36`
defines the quotient factors, and lines 64–65 and 108–110 define the norm product.
`Basic.lean:719` supplies integral slash-translate vanishing.
`CongruenceSubgroups.lean:187` and `ArithmeticSubgroups.lean:107–135` supply finite
index and arithmeticity. `mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean:42,70`
turn filter bounds into a common height. `SlashActions.lean:155–156` identifies the
integral and real matrix slash actions. An rg search for
`fd_norm_bound|norm_domination|coset_norm` across `project/Definitions`
and mathlib's modular-form directory returned no matches. The structured research
record has exactly one `reference_use` entry with source `local-project`.

Fresh local evidence is in `.humanize/rlcr/2026-10-08_16-35-33/validation/`, including
the scoped diagnostic sources, completed body/context build logs, `build-results.json`,
`source-dependency-audit.json`, protected-artifact digests, `reference-use.json`, and
`complete-source.diff`. The freshly requested simplifier agent independently reviewed the selected
proof and found no defect or worthwhile simplification. The round tracker,
defines the quotient factors, and lines 64–65 and 114–116 define the norm product.
`Basic.lean:719` supplies integral slash-translate vanishing.
`CongruenceSubgroups.lean:187` and `ArithmeticSubgroups.lean:107–135` supply finite
index and arithmeticity. `mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean:42,70`
turn filter bounds into a common height. An exact-word rg search for
`f036cc6b1f_fd_norm_bound|norm_domination|norm_bound` across `project/Definitions`
turn filter bounds into a common height. An rg search for
`fd_norm_bound|norm_domination` across `project/Definitions`
and mathlib's modular-form directory returned no matches. The structured research
record has exactly one `reference_use` entry with source `local-project`.

Fresh local evidence is in `.humanize/rlcr/2026-10-08_16-35-33/validation/`, including
the scoped diagnostic sources, completed body/context build logs, `build-results.json`,
`source-dependency-audit.json`, protected-artifact digests, `reference-use.json`, and
`complete-source.diff`. The freshly requested simplifier agent independently reviewed the selected
proof and found no defect or worthwhile simplification. The round tracker,
contract, summary, and raw logs remain ignored runtime metadata; this report provides
the durable committed validation handoff.

## BitLesson Delta

- Action: none
- Lesson ID(s): NONE
- Notes: The lesson file has no entries; no verified repair for the frozen context was found.
