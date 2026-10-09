# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1.ssl_tail_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. For every y≥y₀, apply the increment hypothesis with t=y. It gives 0=‖f(y)−f(y)‖≤e(y), so the error bound is nonnegative wherever it is required.
2. Fix ε>0. Since e(y)→0, there is a real T₀ such that e(u)<ε for every u≥T₀. Put T=max(y₀,T₀).
3. Let s,t≥T. If s≤t, the hypothesis gives ‖f(t)−f(s)‖≤e(s)<ε. If t≤s, it gives ‖f(s)−f(t)‖≤e(t)<ε, and symmetry of the norm of a difference gives the same bound for ‖f(t)−f(s)‖. Thus all pairs of values beyond T have distance less than ε. This is the Cauchy criterion for the image of the filter at +∞ under f.
4. The filter at +∞ on ℝ is nontrivial, and ℂ is complete. The Cauchy property therefore supplies b∈ℂ with f(t)→b as t→+∞.
5. Fix y≥y₀. For every t≥y, the increment hypothesis gives ‖f(t)−f(y)‖≤e(y). By continuity of subtraction by the fixed value f(y) and of the norm, the left side tends to ‖b−f(y)‖. Since the real interval (−∞,e(y)] is closed, this eventual inequality passes to the limit, giving ‖b−f(y)‖≤e(y). Finally, ‖f(y)−b‖=‖b−f(y)‖. Since y was arbitrary, b satisfies both conclusions.

## Key steps

1. Derive nonnegativity of the error bound from the zero increment.
2. Choose a common tail on which e is smaller than a given positive ε.
3. Order any two tail parameters and use symmetry to establish the Cauchy criterion.
4. Use completeness of ℂ to obtain the limit.
5. Pass each fixed-height increment bound to the limit and reverse the difference by norm symmetry.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `rg -n 'scalar_strip_limit|strip_segment_bounds|tail_modulus_limit|polynomial_exp_tail' project`
- `rg -n 'integral_eq_sub_of_hasDerivAt|norm_integral_le_of_norm_le|complexToReal_fderiv|cauchySeq_iff|cauchySeq_tendsto_of_complete' mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean mathlib/Mathlib/Analysis/Complex/RealDeriv.lean mathlib/Mathlib/Topology/MetricSpace/Cauchy.lean mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `rg -n 'p02_es_177ebb5a_ssl_segment_estimates|p02_es_177ebb5a_ssl_tail_limit' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes Submission.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_ssl_decomposition_typecheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/RealDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Topology/MetricSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/tmp/p02_ssl_decomposition_typecheck.lean`

The snapshot-relative rg commands ran from the specified snapshot root. Its project search found no matches for the four requested strip-limit or weight-lemma identifiers. The inspected mathlib files provide restriction of complex derivatives to real derivatives, the vector-valued fundamental theorem of calculus, norm-integral bounds, a Cauchy criterion allowing real indices, and convergence by completeness. The manifest records project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; the installed mathlib HEAD matches and its working tree is clean. Both proposed types successfully elaborated after import Submission with Lean 4.33.1. Transitive axiom queries for the six cited library declarations returned only propext, Classical.choice, and Quot.sound. Both proposed names were absent from the active DAG and searched declarations. These checks validate the interfaces and library references, not acceptance of unimplemented child proofs.
