# Selected pullback point equivalence: implementation audit

This record concerns only `Submission.p07_flp_point_equiv_857cd4d38c`, node
`root.full_level_quotient-a1.full_level_pullback-a1.pullback_point_equivalence-a1`.
It does not assert comparator acceptance or prove the enclosing root theorem.

## Candidate and scope

The existing candidate was introduced by `8ac90b1` and inspected at
`89409226687ea7862bb7ca26dc29d14086a99e45` in the 2026-10-08 16:17:26
RLCR round. Its `Submission.lean` SHA-256 is
`fc148b20f2f93b932dbd898b3ccd5caad0fe6d80`. Its `Submission.lean` SHA-256 is
`ce7f97a2175fe0fece630c86908254333621b36c` in the 2026-10-08 14:03:36
`fa849f7f13845977193811f4b026ad216d9d7b81` in the 2026-10-08 15:01:17
RLCR round. Its `Submission.lean` SHA-256 is
`fc148b20f2f93b932dbd898b3ccd5caad0fe6d80`. Its `Submission.lean` SHA-256 is
`ce7f97a2175fe0fece630c86908254333621b36c` in the 2026-10-08 14:03:36
RLCR round. Its `Submission.lean` SHA-256 is
`81d0a9d64dee7d82cd27ac069c5dde7a4617d51a74ca4899b6fe5ef3dfe4002b`.
The entire source prefix from frozen proof base
`8cb34c690b020247caaf2f18f9cb6fbab8d526f6` is byte-identical. The complete Lean
diff adds 72 lines containing only the selected declaration and its namespace.
There are no new named helpers, imports, axioms, unsafe mechanisms, or placeholders.
The root specification's existing placeholder remains outside this node's proof.

The authoritative accepted proof is
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1-full-level-pullback-a1-pullback-point-equivalence-a1/parent-supplied-natural-proof.md`,
SHA-256 `55a9a4c9a4c55b0a8e44bd3dd6094d0753cd57fd71f430b00de51f979d63ec4d`.
This audit does not revise that proof or reopen decomposition.

## Correspondence with the accepted proof

1. The local forward map `F` composes a point with `g`; pullback commutativity
   establishes its equation over the base.
2. The local inverse `I` is the pullback lift of a target point and `t`.
3. The lift projection identities and `IsPullback.hom_ext` prove the two inverse
   laws. Subtype extensionality discards only membership proof differences.
4. The multiplication clause of `IsPullbackVia` gives the local `map_mul` fact.
5. The image of the source identity is idempotent. The explicit target group
   laws cancel that idempotence and prove the local `map_one` fact.
6. Induction on the natural number, using the defining equations of `nsmulPt`,
   proves preservation of every repeated sum.
7. The action clause and associativity prove compatibility with `pushPt`.

All hypotheses and all five conjuncts match the selected frozen type. A requested
read-only code simplifier review found no concrete defect or useful simplification
and recommended retaining the implementation. That review was not comparator
acceptance.

## Reference use

`reference_use` contains exactly one source: **local-project**.

Snapshot root:
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89`.
Its `manifest.json` pins project `73257f1e32d99b75813b037f28a5cf45a2db886d`
and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Both snapshots and all nine installed `lake-manifest.json` dependencies were
checked clean at their pinned revisions in this round. These source checks do
not independently authenticate cached build artifacts.

Queries run with `rg` against this snapshot:

- `IsPullbackVia|nsmulPt|def pushPt`
- `lift_fst|lift_snd|theorem hom_ext|noncomputable def lift`
- `def IsPullbackVia|structure RelativeGroupLaw|def pushPt|def SchemeHomOver`
- `IsPullbackVia|pushPt`
- `p07_flp_point_equiv|pullback_point_equiv|nsmulPt.*natural`
- `IsPullbackVia|def nsmulPt|def pushPt|structure RelativeGroupLaw|def SchemeHomOver|p07_flp_point_equiv|pullback_point_equiv`
- `lift_fst|lift_snd|hom_ext|noncomputable def lift`
- `SchemeHomOver.*:=|def SchemeHomOver|abbrev SchemeHomOver`
- `p07_flp_point_equiv|pullback_point_equiv|nsmulPt.*natural|theorem.*nsmulPt|lemma.*nsmulPt`

Inspected files, relative to the snapshot root:

- `project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean:31`: the
  pullback, multiplication, and action clauses required by the proof.
- `project/Definitions/Def_CerednikDrinfeld_QMModuli.lean:28`: `mapPt`, the
  `pushPt` abbreviation, and the recursive `nsmulPt` definition at line 45.
- `project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean:78`: the
  explicit multiplication, identity, inverse, associativity, and cancellation
  fields. The proof uses these fields directly without an auxiliary instance.
- `project/Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean:23`:
  `SchemeHomOver` is the subtype of morphisms satisfying the base equation.
- `mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean:106`:
  `lift`, its projection equations, and `hom_ext` at line 125.

The last query returned no matches (exit 1): the pinned project contains no
selected theorem or matching `nsmulPt` naturality lemma. Reused declarations are
pinned upstream infrastructure, not newly invented dependency nodes.

## Current author validation

The 2026-10-08 16:17:26 round re-read the accepted proof and independently
The 2026-10-08 14:03:36 round re-read the accepted proof and independently
The 2026-10-08 15:01:17 round re-read the accepted proof and independently
The 2026-10-08 14:03:36 round re-read the accepted proof and independently
checked the existing implementation. A fresh read-only simplifier review found
no concrete improvement or defect and recommended retaining the proof unchanged.
No Lean source change was needed or made in this round.

With pinned Lean 4.33.1, the selected-declaration diagnostic checks an `example`
against the literal frozen type from the selected DAG record, with warnings fatal
and the project options applied. It exits zero, and `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. This diagnostic intentionally
omits the inherited root declaration and attribute commands; it is not an exact
comparator result or full-source build acceptance.

The actual full-source warning-fatal check exits one with four errors:

- `Submission.lean:13`: unknown `AlgebraicGeometry.Scheme.Hom.opensMapFinal`.
- `Submission.lean:14`: unknown
  `GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase`.
- `Submission.lean:15`: unknown
  `RegularLocalRingQuotientAscent.dualNumberFst_apply`.
- `Submission.lean:22`: the inherited root declaration uses `sorry`.

All errors occur in the unchanged frozen prefix. No placeholder belongs to the
selected theorem. The entire tracked file-change inventory since the frozen proof
base contains only `Submission.lean` and this audit. Protected problem and library
sources remain unchanged. The trusted build boundary remains a controller concern;
this candidate does not alter it or suppress its diagnostics.

Evidence is retained under `.humanize/rlcr/2026-10-08_16-17-26/` in
`round-0-full-build.log`, `round-0-selected-diagnostic.log`,
`round-0-source-audit.json`, `round-0-source.diff`,
`round-0-reference-use.json`, `round-0-dependency-audit.json`, and
`round-0-simplifier-review.md`.
The round uses the authoritative v8 implementation plan. The exact-type diagnostic
reads the literal `lean_statement` from the selected DAG record, checks an
`example` against that independent type, and prints the selected theorem's
transitive axioms. The full-source command uses the pinned Lean 4.33.1 toolchain
and `-DwarningAsError=true` with all four project options. Both checks were rerun
in this round: the supplemental diagnostic exited zero and the full-source check
exited one with precisely the four diagnostics listed above. `git diff --check`
against the proof base also passed. The two snapshots and all nine installed
dependencies were rechecked clean and at their pinned commits.
Evidence is retained under `.humanize/rlcr/2026-10-08_14-03-36/` in
Evidence is retained under `.humanize/rlcr/2026-10-08_15-01-17/` in
`round-0-full-build.log`, `round-0-selected-diagnostic.log`,
`round-0-source-audit.json`, `round-0-source.diff`,
`round-0-reference-use.json`, `round-0-dependency-audit.json`, and
`round-0-simplifier-review.md`.
The round uses the authoritative v8 implementation plan. The exact-type diagnostic
reads the literal `lean_statement` from the selected DAG record, checks an
`example` against that independent type, and prints the selected theorem's
transitive axioms. The full-source command uses the pinned Lean 4.33.1 toolchain
and `-DwarningAsError=true` with all four project options. Both checks were rerun
in this round: the supplemental diagnostic exited zero and the full-source check
exited one with precisely the four diagnostics listed above. `git diff --check`
against the proof base also passed. The two snapshots and all nine installed
dependencies were rechecked clean and at their pinned commits.
Evidence is retained under `.humanize/rlcr/2026-10-08_14-03-36/` in
`round-0-full-build.log`, `round-0-selected-diagnostic.log`,
`round-0-source-audit.json`, `round-0-source.diff`,
`round-0-reference-use.json`, and `round-0-simplifier-review.md`.
These local round artifacts are ignored by Git. The exact candidate commit and
fresh comparator outcome are recorded in the round summary after this audit is
committed; this text makes no claim of comparator success.

The inherited root placeholder is outside the selected child's proof. Its
whole-file warning is recorded for transparency; child warning acceptance is
determined by the configured comparator's frozen baseline. The three unknown
attribute names are a separate inherited compilation problem. Neither condition
justifies editing the protected prefix or treating the isolated diagnostic as
comparator acceptance.

## Verification boundary

The implementation requires the exact selected-node comparator on a clean
committed candidate, with exit zero and `Your solution is okay!`. A passing
isolated type check, a review, or the presence of this audit cannot replace that
gate. Warning-fatal full-source and transitive-axiom diagnostics, final candidate
identity, and the actual comparator outcome are recorded in the current RLCR
round summary. Fresh independent acceptance, publication, and the DAG transition
remain outer-controller tasks.

## BitLesson Delta

- Action: none
- Lesson ID(s): NONE
- Notes: The project lesson file contains no entries. No lesson was added.
