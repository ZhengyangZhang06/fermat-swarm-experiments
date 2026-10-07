# Coset norm bound: author validation

Selected node: `root.gamma0_finite_dimensional-a1.coset_norm_bound-a1`.
Only tracked theorem: `Submission.f036cc6b1f_fd_norm_bound`.

The existing implementation in `Submission.lean` is retained unchanged. It realizes the
accepted parent proof: the finite coset factors tend to zero, so they are simultaneously
bounded by one above a common height; separating the identity factor yields the bound
with `C = 1`. The requested simplifier review found no justified change.

The exact type remains:

```lean
∀ (M : ℕ) [NeZero M] (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2), ∃ C Y : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, Y ≤ z.im → ‖ModularForm.norm (MonoidHom.range (Matrix.SpecialLinearGroup.mapGL ℝ : Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℝ)) f z‖ ≤ C * ‖f z‖
```

## Fresh author checks, 2026-10-07, round started 20:19:24 UTC

- Lean 4.33.1, `-DwarningAsError=true`: the unchanged selected theorem in a fresh diagnostic importing
  `Definitions.Def_ModularForm_HeckeOperatorForms` passes, including an anonymous check
  against the literal frozen type.
- Transitive axiom reports for the selected theorem, `ModularForm.norm`,
  `CuspFormClass.zero_at_infty_slash`, and `CongruenceSubgroup.instFiniteIndexGamma0`
  contain only `propext`, `Classical.choice`, and `Quot.sound`.
- All nine dependency repositories have clean status and their manifest-pinned HEADs.
- Five inspected mathlib files and all 81 snapshot project Definitions files match the
  local reference snapshot byte-for-byte.
- The complete inherited source diff preserves the frozen Submission prefix. Its only
  new theorem is the selected declaration, with no local placeholders, new axioms,
  unsafe mechanisms, or weakened statement. The other inherited change is a runtime
  skill ignore rule in `.gitignore`.

**Required validation remains blocked.** The fresh diagnostic retaining the frozen imports
and attribute commands, while excluding the unrelated root theorem, exits 1. The two
grouped commands fail before this node's proof. A fresh exact-name provider search across
snapshot `project/Definitions` and `mathlib/Mathlib` returns no matches for their 15 targets;
the earlier individual-target diagnostic remains available in the previous round's evidence.
The first errors name
`FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions`
and `FreyPackage.ModMCarrier.coe_rescaleLin_apply`. Thus the passing diagnostic without
the attribute commands is not full-context acceptance. The unchanged whole source also
reports the inherited root placeholder under warning-fatal checking; no root proof or
root comparator is part of this node's task.

The latest prior controller artifact, `comparator-v4.log`, records exit 1 for request
`6622e79c98cb49149b166263fbe5e470`, with the same missing constants in the frozen challenge.
The earlier local polling process (PID 4568) was observed as a zombie and was not restarted
or canceled. No controller state or previous request was modified.

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
defines the quotient factors, and lines 64–65 and 114–116 define the norm product.
`Basic.lean:719` supplies integral slash-translate vanishing.
`CongruenceSubgroups.lean:187` and `ArithmeticSubgroups.lean:107–135` supply finite
index and arithmeticity. `mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean:42,70`
turn filter bounds into a common height. Searches for the exact selected name and
norm-bound variants in `project/Definitions` returned no matches.

Fresh local evidence is in `.humanize/rlcr/2026-10-07_20-19-24/validation/`, including
the scoped diagnostic sources, completed body/context/full-source build logs, `build-results.json`,
`source-dependency-audit.json`, protected-artifact digests, the provider search log, and
`complete-source.diff`. The requested simplifier agent independently reviewed the selected
proof and found no defect or worthwhile simplification. The round tracker,
contract, summary, and raw logs remain ignored runtime metadata; this report provides
the durable committed validation handoff.

## BitLesson Delta

- Action: none
- Lesson ID(s): NONE
- Notes: The lesson file has no entries; no verified repair for the frozen context was found.
