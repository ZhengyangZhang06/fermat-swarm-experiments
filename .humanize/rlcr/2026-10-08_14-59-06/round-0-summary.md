# Round 0 Summary

## Outcome

The existing selected-node implementation was audited and retained unchanged. **AC2 is unmet:** both the literal warning-fatal build and the configured selected-node comparator exit 1 in the inherited frozen scaffold. Comparator request `6ce3add7f60b402b963ac65ad9ce6c3d` ran against clean commit `296be36f0e5deb175c02578a1c80870f80d4bd2d`, returned with the same HEAD and a clean worktree, and did not print `Your solution is okay!`. No proof acceptance is claimed.

## Implementation and review

Read the frozen problem and accepted seven-step parent proof. Inspected all 117 added lines of `Submission.lean` against proof base `378b6d892615f2f4fb2ff1319cb447513bf85bef`. The only added theorem is `Submission.p07_cre_group_law_857cd4d38c`; all auxiliary arguments are local bindings. The full child type equals the authoritative DAG statement modulo whitespace, and the entire frozen source prefix is byte-identical. No hypotheses, conclusions, imports, attributes, definitions, or protected files were changed.

The proof constructs inverse base morphisms, preserves the underlying scheme maps in relative-point equivalences, proves compatibility with precomposition, and transfers the group laws, naturality, and commutativity by injectivity. The user-requested read-only [simplifier review](round-0-simplifier-review.md) found no warranted changes. That review does not substitute for outer acceptance.

## Validation evidence

- [Source and dependency audit](round-0-audit.json): all nine installed package checkouts and both reference checkouts are clean at their exact pins. Complete candidate changes since the proof base are `Submission.lean` and the inherited `.gitignore` runtime-skill exclusion. No additional named child declarations, forbidden proof tokens, or frozen-prefix changes were found.
- [Warning-fatal build](round-0-build.log), [command/result](round-0-build-result.json): exit 1. `Submission.lean:13–15` reports unknown constants `AlgebraicGeometry.Scheme.Hom.opensMapFinal`, `GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase`, and `RegularLocalRingQuotientAscent.dualNumberFst_apply`; line 22 reports the inherited root's `sorry`. These are the first reported targets of the three attribute commands, not an exhaustive inventory of missing constants. No child-proof error was reported.
- [Transitive axiom diagnostic](round-0-axioms.log), [result](round-0-axioms-result.json): the selected child depends only on `propext`, `Classical.choice`, and `Quot.sound`. The scratch file preserves the full original source and appends only `#print axioms Submission.p07_cre_group_law_857cd4d38c`. The process still exits 1 on the inherited scaffold; this is limited axiom evidence, not successful compilation or acceptance.
- [Configured comparator output](round-0-comparator.log), [terminal result](round-0-comparator-result.json): one exact selected-node request, with `HF_TOKEN` removed. Exit 1 occurred while building `challenge/Submission.lean` for export, at the same three unknown attribute targets. The inherited root also emits its placeholder warning. The traceback is through the served `verify_prepared` → `compare` → `export` path; child-proof comparison was not reached. The full raw-output SHA-256 is `360f362807cb2b73784ea12ed7b7838268ed55821781095b26378815c68bdfa1`. No root/whole-benchmark comparator, alternate verifier, changed context, or repeated request was used.

## Scope and task accounting

Initialized the goal tracker and Round 0 contract before implementation. TaskCreate/TaskUpdate/TaskList are not exposed in this environment; the tracker records each task's lane, state, AC, and `coding -> claude` routing. BitLesson was reread before tasks/subtasks; selection was always NONE because it contains no entries.

Another round briefly staged and committed its documentation (`9740a14`), after which an external actor reset HEAD to `296be36`. This round did not stage, reset, delete, or take ownership of those files. Fresh checks confirmed a clean worktree before the configured comparator. The missing sandbox launcher was handled through the execution tool's explicit escalation path.

This round changes documentation/evidence only. Independent comparator rerun, final prose/Lean acceptance, wiki publication, DAG transition, and issue/PR integration remain outer-controller tasks. No loop-control state, theorem proof, controller verifier, service, or authoritative claim was modified.

The documentation commit for this round records failed gates; it is not a newly verified proof candidate. The exact checked proof candidate remains `296be36f0e5deb175c02578a1c80870f80d4bd2d`. AC1 has source/type/prose-review evidence pending outer verification; AC3's research and handoff evidence is recorded. Successful build and comparator completion are explicitly deferred because changing the inherited frozen context or the served verifier is outside this node's authorized implementation boundary. This defect cannot be repaired by altering the correctly scoped child proof. Return the blocker to the recursive controller without restarting decomposition or claiming the node proved.

The raw comparator log preserves eight trailing spaces emitted by upstream linter messages so its recorded digest remains valid. The staged whitespace check excludes only this unmodified raw output; all other round artifacts are checked normally.

## Reference use

```json
{
  "reference_use": [
    {
      "source": "local-project",
      "snapshot": "/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89",
      "project_commit": "73257f1e32d99b75813b037f28a5cf45a2db886d",
      "mathlib_commit": "db584cd6d46c92f209a44c0f1c829460d327499d",
      "evidence": "round-0-reference-use.json",
      "findings": "RelativeGroupLaw.lean:68,78–113 supplies precomposition, the required group-law fields, and commutativity. NeronModelPropertyBundleCarrier.lean:23 supplies SchemeHomOver's subtype representation. Mathlib/AlgebraicGeometry/Spec.lean:273–274 supplies functoriality. No rebase/ringEquiv/transport match in the group-law file, no selected theorem-name match in the pinned project, and no match for the exact missing-name query in Definitions/P2M/Mathlib.",
      "verification_limits": "Pins and cleanliness checked; selected transitive axioms reported standard only; full-file build and exact comparator exit 1 in inherited context. The comparator fails before child comparison; acceptance remains unmet."
    }
  ]
}
```

The [reference-use record](round-0-reference-use.json) contains the exact `rg` queries, actual absolute paths, line findings, and no-match results. No network search or Lean-Eval acquisition was performed.

## BitLesson Delta

Action: none
Lesson ID(s): NONE
Notes: No lessons exist, and no new operational fix was established. The knowledge base was left unchanged.
