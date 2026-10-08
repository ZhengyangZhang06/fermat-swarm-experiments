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
