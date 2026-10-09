# Exact Hecke commutation candidate audit

Selected node: `root.good_hecke_commute-a1`.
Only tracked declaration: `Submission.f036cc6b1f_hecke_commute`.

The inherited candidate is retained without Lean edits. This audit is not proof acceptance.

## Frozen type

```lean
∀ (M : ℕ) [NeZero M] (p r : ℕ) (hp : p.Prime) (hr : r.Prime)
  (hpM : ¬ p ∣ M) (hrM : ¬ r ∣ M),
  (CuspForm.heckeTLin 2 hp hpM).comp (CuspForm.heckeTLin 2 hr hrM) =
    (CuspForm.heckeTLin 2 hr hrM).comp (CuspForm.heckeTLin 2 hp hpM)
```

The declaration type matches the accepted parent-child handoff after whitespace normalization. Its proof uses the existing q-coefficient identity and uniqueness theorem, handles equal primes by proof irrelevance, and handles distinct primes by four divisibility cases. The author-side simplifier found no necessary correction or useful simplification.

## Provenance and source checks

- The frozen prefix of `Submission.lean` is byte-identical to proof base `674e47109a2c121849b48a3754cad6d3c648d80e`. Only the selected theorem is added; all intermediate facts are local proof steps.
- No new `sorry`, `admit`, axiom, unsafe declaration, custom elaborator, or option override occurs in the added proof. The root stub remains inherited and out of scope.
- `Definitions/Def_ModularForm_HeckeOperator.lean`, `Definitions/Def_ModularForm_HeckeOperatorForms.lean`, and `P2M/Sol/S_ModularForm_mdifferentiable_heckeT.lean` match both the proof base and the pinned local-project snapshot byte-for-byte.
- The snapshot manifest pins project `61b5f85556ac71631ccad822e0694511234f7132` and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. All nine installed dependencies are clean at their manifest revisions.
- The pinned P2M file supplies `M4cP1W2.qCoeff_heckeT_class` at line 340 and `M4cP1W2.eq_of_forall_qCoeff_eq` at line 172. These are existing library declarations, not newly introduced dependency nodes.

## Reproduced full-context blocker

On 2026-10-08, the pinned Lean 4.33.1 toolchain command
`lake env lean -DwarningAsError=true Submission.lean` exited 1:

```text
Submission.lean:9:22: unknown constant FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions
Submission.lean:10:18: unknown constant FreyPackage.ModMCarrier.coe_rescaleLin_apply
Submission.lean:12:8: declaration uses sorry
```

Searching the required pinned project snapshot for the two missing names finds only their uses in `Submission.lean` and the original Fermat contract, with no definitions. The frozen commands, imports, parent theorem, handoff, and decomposition were preserved.

The current round's generated diagnostic, source/dependency audit, exact comparator output, and final outcome are kept in `.humanize/rlcr/2026-10-08_13-03-54/`. The diagnostic omits the failing frozen context and cannot establish comparator acceptance. The exact candidate SHA and comparator outcome must be taken from the final round summary; this committed note makes no prospective success claim.

Independent review, theorem-wiki publication, DAG acceptance, and solution-PR integration remain the recursive controller's responsibility.

## Recheck in the 2026-10-08 14:08:23 implementation round

The exact candidate was retained after a separate read-only simplifier review found no necessary correction or useful simplification. Fresh source checks confirm the exact frozen type, unchanged proof-base prefix, one added named theorem, and no prohibited proof mechanisms. The three reused source files again match both the snapshot and proof base; all nine dependencies are clean at their pinned revisions.

Using `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake`, the full warning-fatal `Submission.lean` check again exits 1 with the two missing frozen attribute names and the inherited root `sorry` reported above. An isolated diagnostic containing the unchanged selected theorem and an anonymous check against the handoff type exits 0 with warnings fatal. The theorem, bundled operator, coefficient formula, and coefficient uniqueness lemma each have exactly the transitive axiom set `propext`, `Classical.choice`, `Quot.sound`. The diagnostic omits the frozen prefix and therefore is not full-context or comparator acceptance.

Current evidence is in `.humanize/rlcr/2026-10-08_14-08-23/`: `source-audit.json`, `full-warning-fatal.log`, `selected-node-diagnostic.log`, and `simplifier-review.md`. The final `round-0-summary.md` records the exact committed candidate and configured child-comparator result. No parent/sibling comparator or new helper theorem is introduced.

## Recheck in the 2026-10-08 15:00:31 implementation round

The inherited selected proof remains unchanged after fresh comparison with the accepted natural proof and a separate read-only code-simplifier review. The frozen type agrees with the current child handoff, whose approved dependency list is empty. The entire source prefix agrees with both the proof base and the frozen problem Markdown; the sole added theorem contains no placeholders, new axioms, or unsafe mechanisms. All nine dependency repositories remain clean at their manifest revisions. The three reused project files match the pinned snapshot and proof base, and the installed QExpansion source matches the snapshot.

Fresh `rg` research in the required snapshot located the exact bundled normalization at `project/Definitions/Def_ModularForm_HeckeOperatorForms.lean:69` and `:96`, the pointwise/coefficient formulas at `project/Definitions/Def_ModularForm_HeckeOperator.lean:118` and `:162`, and the reused coefficient uniqueness/action theorems at `project/P2M/Sol/S_ModularForm_mdifferentiable_heckeT.lean:172` and `:340`. The Fourier expansion and uniqueness foundations are in `mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean:190` and `:727`. A search for `heckeTLin.*commut|commut.*heckeTLin` in the snapshot project and mathlib modular-forms directories returned no matches. Searching the two unavailable frozen attribute names returned only uses in the original Submission and Fermat contract, with no definitions.

The pinned Lean 4.33.1 full-file warning-fatal check again exits 1 with exactly the two missing attribute names and inherited root `sorry`. The selected-node diagnostic exits 0 with warnings fatal and verifies the complete handoff type. The selected theorem, bundled Hecke operator, coefficient definition theorem, coefficient action, and coefficient uniqueness each have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom closure. Because the diagnostic omits the failing frozen context, it does not establish configured-comparator acceptance.

This round's local evidence is under `.humanize/rlcr/2026-10-08_15-00-31/`: `audit-local.py`, `source-audit.json`, `lean-results.json`, `full-warning-fatal.log`, `selected-warning-fatal.log`, and `simplifier-review.md`. The final round summary records this committed candidate's SHA and the prescribed exact-node comparator's actual outcome. No prospective success or outer acceptance is claimed. TaskCreate/TaskUpdate/TaskList are unavailable in the session; task state is recorded in the initialized goal tracker. BitLesson selection is `NONE` for every task because the knowledge base has no entries.

## Recheck in the 2026-10-08 16:39:30 implementation round

The selected theorem is unchanged. A fresh audit matches its complete type to the current handoff, confirms the empty approved dependency list, and checks the frozen source prefix against both the problem Markdown and proof base. All 98 Lean infrastructure files under `Definitions`, `Theorems`, and `P2M` match the proof base and pinned snapshot byte-for-byte. All nine dependency repositories are clean at their manifest revisions; the installed QExpansion source also matches the snapshot. A separate read-only simplifier review found no defect or useful simplification.

The pinned Lean 4.33.1 warning-fatal full-file check exits 1 with the same two unknown frozen attribute constants and inherited root `sorry`. The selected-node diagnostic, generated from the unchanged candidate and containing an anonymous check against the handoff type, exits 0 with warnings fatal. Its transitive axiom audit covers the theorem, bundled operator, coefficient definition theorem, coefficient action, and coefficient uniqueness; all five use only `propext`, `Classical.choice`, and `Quot.sound`. The diagnostic omits the failing frozen prefix and is not configured-comparator acceptance.

Mandatory local-project searches again locate the coefficient formula and uniqueness in the pinned P2M source. Searches for `heckeTLin.*commut|commut.*heckeTLin|coeffHeckeT.*commut|commut.*coeffHeckeT` return no matches in the snapshot project and mathlib modular-form directories. The unavailable attribute names occur only as uses in the frozen Submission and Fermat files. No protected context, proof handoff, dependency source, or DAG metadata was changed.

Round evidence is in `.humanize/rlcr/2026-10-08_16-39-30/`: `audit-local.py`, `source-audit.json`, `lean-results.json`, `full-warning-fatal.log`, `selected-warning-fatal.log`, and `simplifier-review.md`. The required tracker and contract are initialized there; the final summary will record this commit's exact-node comparator result. No comparator success or independent acceptance is asserted in advance.
