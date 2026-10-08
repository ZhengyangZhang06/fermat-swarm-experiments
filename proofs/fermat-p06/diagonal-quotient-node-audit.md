# Diagonal quotient node: implementation audit

This is an implementation diagnostic, not a proof-acceptance or publication record.

Selected node: `root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1.diagonal_cokernel_product-a1`.
Sole tracked theorem: `Submission.p06_9e0f5043ff_dmc_diagonal_quotient`.
Approved child dependencies: none.

```lean
∀ (R : Type*) [CommRing R] (m : ℕ) (d : Fin m → R),
  Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d)))
    ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R)))
```

## Source and proof audit

On 2026-10-08, the existing implementation at `2b1c11897272afc5def47634d672a6d45018d845`
was reviewed against the accepted parent-supplied proof. It defines the coordinate quotient
map, identifies its kernel with the diagonal image through principal-ideal membership,
proves surjectivity using coordinate representatives, and applies the first isomorphism
theorem. No additional hypotheses are used, including when `m = 0`.

The complete source diff from proof base `35bdf5edb6fc8557cb89f866eb7a167adb49b836`
adds exactly the selected theorem. The original prefix, including its import, attributes,
root statement and placeholder, is unchanged. The selected proof contains no placeholder,
new axiom, named helper declaration, unsafe implementation, or alternate evaluation mechanism.
A separate read-only simplifier review recommended retaining the proof.

`Submission.lean` SHA-256:
`c9d10ca8321010f01e3076928d5e04f3de7709226eb1e4b8052f4391e1ea6f31`.

## Fresh diagnostic results

Using Lean 4.33.1 and the project's frozen options, the exact theorem extracted under its
original import passed `lake env lean -DwarningAsError=true -DautoImplicit=false
-DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000
-Dbackward.isDefEq.respectTransparency.types=false` with exit zero. An explicit `#check`
used the frozen type above. Transitive `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound` for the selected theorem and reused infrastructure.

All nine installed dependencies matched `lake-manifest.json` revisions and had clean
tracked files. The four reused library files listed below and the direct project import
matched the reference snapshot byte for byte.

The warning-fatal check of the full unchanged `Submission.lean` exited 1:

- Line 9: unknown `AlgebraicCurve.IsCurveOver.instNontrivialKaehler`.
- Line 10: unknown `AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply`.
- Line 11: unknown `AlgebraicCurve.SemilinearAut.coe_torsion_smul`.
- Line 14: the inherited root declaration uses `sorry`.

The extracted diagnostic excludes those inherited commands and the root declaration, so
its success is not full-context or comparator acceptance. Editing the selected theorem
cannot repair the comparator's separate frozen challenge. No contract, dependency,
verifier, controller, or source-context repair is claimed here. The configured exact-node
comparator must still pass, followed by the outer controller's independent review.

## Reference use

Exactly one `reference_use` source: **local-project**.

Snapshot: `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`.
Its `manifest.json` pins project `956e8c600d8b95b46948ae5e37b13930b5f3d06b`
and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Paths below are relative to that snapshot.

- `mathlib/Mathlib/LinearAlgebra/Isomorphisms.lean:47` defines
  `LinearMap.quotKerEquivOfSurjective` through the quotient-to-range equivalence.
- `mathlib/Mathlib/LinearAlgebra/Quotient/Defs.lean:98,236,252` supplies quotient
  zero membership, quotient-map surjectivity, and quotient transport along equality.
- `mathlib/Mathlib/RingTheory/Ideal/Span.lean:181` identifies principal-ideal membership
  with divisibility.
- `mathlib/Mathlib/Data/Matrix/Mul.lean:752` proves the diagonal coordinate formula.
- `project/Definitions/Def_AlgebraicCurve_IsCurveOver.lean:41` and
  `project/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean:311` contain two of
  the attribute targets; the original direct import does not expose them.
- `project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean:1-5` has the unchanged
  five direct imports. `rg -n 'frobNormRingHom' SNAPSHOT/project/Definitions` returned
  no matches. This is a bounded textual finding, not an assertion about missing external sources.

The targeted snapshot query
`rg -n --glob '*.lean' 'cokernel.*(isUnit|IsUnit|diagonal)|[Dd]iagonal.*[Cc]okernel|[Cc]okernel.*[Dd]iagonal|range_mulVecLin.*pi|mulVecLin.*quot' SNAPSHOT`
returned no matches. Focused searches for `quotKerEquivOfSurjective`, `quotEquivOfEq`,
`mkQ_surjective`, `mk_eq_zero`, `mem_span_singleton`, and `mulVec_diagonal` located
the inspected library declarations above. These are existing pinned declarations,
not new helper nodes. No network search was used.

## Evidence locations

Local round artifacts are under `.humanize/rlcr/2026-10-08_17-51-42/`:
`NodeCheck.lean`, `node-build.log`, `node-build.json`, `submission-build.log`,
`submission-build.json`, `source-audit.json`, `source-diff.patch`,
`dependency-audit.json`, `reference-compatibility.json`, and
`code-simplifier-review.md`. The round summary records the subsequent exact comparator
result and its candidate SHA. Runtime artifacts do not change proof-acceptance status.

## BitLesson Delta

- Action: none
- Lesson ID(s): NONE
- Notes: The lesson database is empty. No verified repair was made.
