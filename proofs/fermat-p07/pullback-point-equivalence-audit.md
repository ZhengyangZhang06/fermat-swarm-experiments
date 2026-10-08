# Selected pullback point equivalence: implementation audit

This record concerns only `Submission.p07_flp_point_equiv_857cd4d38c`, node
`root.full_level_quotient-a1.full_level_pullback-a1.pullback_point_equivalence-a1`.
It does not assert comparator acceptance or prove the enclosing root theorem.

## Candidate and scope

The existing candidate was introduced by `8ac90b1` and inspected at
`fc148b20f2f93b932dbd898b3ccd5caad0fe6d80`. Its `Submission.lean` SHA-256 is
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
