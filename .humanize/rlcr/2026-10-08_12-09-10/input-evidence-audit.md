# Selected-node input evidence audit

The Lean candidate is unchanged from `356da64ad1a03c4e80afab91ada09bf46160ce73`. This round audits only `Submission.p02_es_177ebb5a_crl_horizontal_difference_limit` and investigates the inaccessible controller evidence reported by the outer reviewer. It does not claim independent proof acceptance.

## Local source integrity

- Frozen proof base: `d6db90e64b7559d9a9c9281a36bcabd23e4c2861`.
- Complete source diff from that base: only 75 added lines in `Submission.lean`, containing exactly the selected theorem and local proof steps. Removing that declaration reproduces the base file byte for byte, including the original root placeholder and inherited declarations.
- The theorem statement matches the selected DAG type after whitespace removal; the committed dispatch handoff and run handoff agree as JSON; dependencies are empty.
- `Submission.lean` Git blob: `039468e53ddde951a29521c64d98e6ca628ab9c5`.
- `Submission.lean` SHA-256: `ec02086ddbaa93b7b2c06e9f587b255645de4e962a3fd35ffcda7a7e4c89a673`.
- Canonical handoff SHA-256: `8faf29dbd0977bfb9c7c2c2ebae086a437266cb0fdbb189f4488dd71966bd34b`. The controller hashes compact UTF-8 model JSON, not the pretty-printed file bytes; both representations were distinguished in the audit.
- No new named helpers, placeholders, axioms, unsafe mechanisms, changed imports, or protected Lean/configuration files. `git diff --check` passes.
- All nine `lake-manifest.json` dependency checkouts match their revisions and have empty full porcelain status. The three mathlib reference files below match installed sources byte for byte.

These are local source checks. They do not prove which files a remote process actually consumed.

## Unresolved controller evidence access

The previous reviewer request was `2b524bf00d294b1f9eefdf21fcbd47ad`. Its reported directory does not exist in this worker's filesystem:

`/mnt/data/zhengyang-workspace/fermat-remote-verification.q96OJN/hoa80/2b524bf00d294b1f9eefdf21fcbd47ad/output/result`

Read-only inspection found:

- `/runtime/flows/math-lean-flow/scripts/swarm-compare.py` validates the returned request/revision identity and prints `result['output']`. It does not transfer artifact files.
- `/runtime/flows/math-lean-flow-cache-diagnostics-v2/_recursive_lean/remote_verification.py`, `VerificationService.result`, returns request ID, revision, state, return code, and log text.
- `/runtime/flows/math-lean-flow-cache-diagnostics-v2/_recursive_lean/swarm_broker.py:331` exposes GET `/issues` and `/health`, plus the existing POST claim/status/verification routes. There is no artifact retrieval route.
- `/runtime/flows/math-lean-flow-cache-diagnostics-v2/scripts/swarm-verify-frozen-node.py:221` checks private prepared inputs and final evidence on the controller, then prints the private result path. This does not make that path available to the worker/reviewer.

The controller must provide a read-only export or mount containing the authentic `prepared.json`, `evidence.json`, actual `challenge/Challenge.lean`, challenge/base and solution `Submission.lean` files, generated `solution/Solution.lean`, and the prepared source inventory. The export must preserve the request/revision binding and allow independent checking of the recorded hashes. No worker-generated substitute or echoed comparison-identity digest meets that requirement.

This node implementation did not change the broker, verifier, cluster services, mounts, ownership records, or loop state. Independent reviewer acceptance remains pending actual-input access.

## Reference use

`reference_use` contains exactly one entry:

```json
[
  {
    "source": "local-project",
    "queries": [
      "p02_es_177ebb5a_crl_|eichlerShimuraMap_injective|primitive.*limit|common_ray_limit",
      "p02_es_177ebb5a_crl_|primitive.*limit|common_ray_limit",
      "tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero|integral_eq_sub_of_hasDerivAt|norm_integral_le_of_norm_le_const"
    ],
    "files": [
      "/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json",
      "/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean",
      "/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean",
      "/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean",
      "/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean"
    ],
    "conclusion": "Manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Project search finds the frozen injectivity declaration; the second query exits 1 with no selected-node/primitive-limit/common-ray matches. Inspected mathlib declarations at Asymptotics.lean:141, FundThmCalculus.lean:1148, and Basic.lean:769 supply exponential decay, FTC, and the integral norm bound used by the unchanged proof. Installed dependency revisions are clean and pinned, and those files are byte-identical to the snapshot. No new helper is attributed to this node."
  }
]
```

## BitLesson Delta

Action: none

Lesson ID(s): NONE

Notes: The required BitLesson file contains no entries. No new lesson is added because the controller evidence-access defect has not been repaired or validated.
