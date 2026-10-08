# Selected theorem simplifier review

Read-only review by `/root/simplifier_review`, requested by the builder under the user's simplifier instruction. BitLesson selection: NONE. No files changed, builds run, or comparator requests made by the reviewer.

- The declaration matches the frozen type.
- The proof follows the accepted coefficient selection and square-zero matrix construction; `1 + N` is the two-sided inverse of `1 - N`.
- The shared multiplication identity gives both requested conclusions.
- The proof covers `m = 0`, zero pivots, zero divisors, and the trivial ring without extra assumptions.
- `hmul` and `hsq` are local proof steps, not extra theorem nodes.
- No useful simplification or selected-theorem defect was found. Retain the current proof.

This is a source/simplification review, not the outer-controller independent comparator gate or proof acceptance.
