# Compatible valuation-order invariance: preservation verification

Selected node: `root.rational_adjoin_principal-a1.principal_alg_equiv-a1.compatible_order_invariance-a1`.

The sole tracked declaration is
`Submission.p06_9e0f5043ff_pae_compatible_order_invariance` in `Submission.lean`.
There are no comparator-approved child dependencies and no new named helpers.

## Preservation repair

The latest review requires the complete frozen source from proof-base commit
`977ae076f08b2e1f0a36e5c83fb48da8176b61ce` to remain verbatim, including
`open AlgebraicCurve` and the inherited root theorem's `sorry`.
Commit `a1e0705d8f53a1f3a18dc18fe51a5cc4aa796594` already contains that repair;
this verification round leaves the Lean source unchanged.

A byte-prefix comparison against `git show 977ae076f08b2e1f0a36e5c83fb48da8176b61ce:Submission.lean`
passes for all 5,160 baseline bytes. Their SHA-256 is
`b004dca1496ade3fb13e18207639dd199dcb7aeb7df210061bf8c375960870bc`.
The complete Lean diff appends only the selected theorem and its namespace,
documentation, and locally scoped `warningAsError=true` option. The theorem
uses no new placeholder, axiom, unsafe mechanism, or named helper. Protected
contracts, library files, dependency pins, and handoff artifacts are unchanged.

## Exact contract and proof correspondence

```lean
∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] (e : E ≃ₐ[K] L) (v : AlgebraicCurve.Place K E) (w : AlgebraicCurve.Place K L) (r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring), (∀ a : v.toValuationSubring, (r a : L) = e (a : E)) → ∀ f : E, f ≠ 0 → w.ord (e f) = v.ord f
```

The implementation follows the supplied accepted proof without revising it:

1. Choose an irreducible uniformizer in the DVR associated with `v`.
2. Transport irreducibility through `r` using the existing `Irreducible.map`.
3. Factor nonzero `f` as a unit times that uniformizer to the power `v.ord f`.
4. Transport the unit using `Units.map`, and use compatibility to identify its ambient value.
5. Apply `e` to the factorization, preserving multiplication and integer powers.
6. Evaluate the resulting expression with `w.ord_unit_smul_zpow`.

A separate read-only simplifier review found no defect or worthwhile simplification,
confirmed exact baseline preservation, and introduced no edits. This review does
not replace the outer controller's independent acceptance.

## Local verification

All nine dependencies in `lake-manifest.json` have clean Git worktrees and exactly
their recorded revisions. The reused project and mathlib files listed below are
byte-identical to the pinned reference snapshot. The toolchain is Lean 4.33.1 at
`/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin`.

The direct command `lake env lean -DwarningAsError=true Submission.lean` exits 1:
the frozen attribute directives at lines 9–11 reference unavailable constants,
and line 14 reports the preserved root placeholder. Those inherited errors are
recorded, not removed from the candidate.

For the supplemental child-only check,
`.humanize/rlcr/2026-10-08_20-00-52/SelectedNodeCheck.lean` copies the exact appended
child source after the original import and adds an anonymous `example` of the
frozen type and `#print axioms` commands. It does not replace `Submission.lean`.
The command below exits 0 without warnings:

```sh
lake env lean -DwarningAsError=true -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false .humanize/rlcr/2026-10-08_20-00-52/SelectedNodeCheck.lean
```

The selected theorem, `Place.exists_unit_mul_zpow`, `Place.ord_unit_smul_zpow`, and
`IsDiscreteValuationRing.exists_irreducible` each report exactly
`[propext, Classical.choice, Quot.sound]`. `Irreducible.map` reports
`[propext, Quot.sound]`; `Units.map` reports `[propext]`.
`git diff --check` passes.

## Reference use

Exactly one `reference_use` entry:

- source: `local-project`
  - Snapshot: `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`.
  - Manifest: `manifest.json` within that snapshot; project revision `956e8c600d8b95b46948ae5e37b13930b5f3d06b`, mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`.
  - `rg -n 'exists_unit_mul_zpow|ord_unit_smul_zpow|exists_irreducible|theorem Irreducible.map|def map '` found the order evaluation and factorization in `project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:153,163`, and uniformizer existence in `mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:105`. The DVR instance at project line 73 was also inspected.
  - A follow-up search and inspection of `mathlib/Mathlib/Algebra/Group/Irreducible/Lemmas.lean:81,92` found `Irreducible.map` as an alias of `MulEquiv.irreducible_iff`, explaining the no-match for a literal `theorem Irreducible.map` search.
  - `rg -n 'def map|val_map'` and file inspection found `Units.map` and its definitional coercion in `mathlib/Mathlib/Algebra/Group/Units/Hom.lean:75,80`.
  - `rg -n 'compatible_order_invariance'` across the snapshot found no matches (exit 1).
  - An intermediate query accidentally omitted `local-references/08e30764522e474f` from two paths; it returned missing-path errors and was corrected before inspection. This was not treated as a no-match result.
  - No network research or other reference corpus was used.

## Committed-candidate gate

After committing this record, run only the user-specified `swarm-compare.py`
command for the selected node on the clean exact commit. Record its SHA,
exit code, success text, and verifier evidence in the ignored round summary at
`.humanize/rlcr/2026-10-08_20-00-52/round-0-summary.md`.
Local compilation alone is not proof acceptance. Fresh reviewer comparison,
theorem-wiki publication, DAG transition, and integration remain outer-controller
tasks after this implementation invocation returns.

## BitLesson Delta

Action: none

Lesson ID(s): NONE

Notes: The required BitLesson file contains no lessons; it was read before each mainline task. No lesson was added or changed.
