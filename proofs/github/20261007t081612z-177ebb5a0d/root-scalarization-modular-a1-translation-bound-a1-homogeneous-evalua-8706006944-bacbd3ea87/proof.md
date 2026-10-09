# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.homogeneous_evaluation_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Homogeneity means that a nonzero coefficient can occur only at an exponent pair whose sum is n. Such pairs are exactly (r,n−r), with 0≤r≤n. Hence R(X,Y)=Σ_{r=0}^n c_r X^rY^(n−r), where each c_r is a monomial coefficient of R and satisfies |c_r|≤b.
2. Evaluate at X=1 and Y=−z to obtain R(1,−z)=Σ_{r=0}^n c_r(−z)^(n−r). The triangle inequality and multiplicativity of the complex norm give |R(1,−z)|≤Σ_{r=0}^n |c_r||z|^(n−r).
3. Set M=max(1,|z|). Then M≥1 and |z|≤M. Since 0≤n−r≤n, one has |z|^(n−r)≤M^(n−r)≤M^n. Each summand in step 2 is therefore at most bM^n, using b≥0.
4. There are exactly n+1 summands. Their sum is at most (n+1)bM^n=(n+1)M^n b, which is the claimed bound. For n=0 this argument has one summand and M^0=1, so it covers that case as well.

## Key steps

1. Enumerate the n+1 possible degree-n monomials.
2. Expand evaluation at (1,−z) and apply the triangle inequality.
3. Bound every monomial evaluation by max(1,|z|)^n.
4. Sum the uniform bounds.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|isBoundedAtImInfty_iff|binaryFormRepSL|eichlerShimuraMap_injective`
- `theorem.*(T_pow|T_zpow)|def T|lemma.*(T_pow|T_zpow)|coe_T|T_smul`
- `integrable.*exp|exp.*integrable`
- `eq_C_of.*comp|comp.*eq_C|periodic|Periodic`
- `norm_eval|eval.*norm|norm.*eval`
- `rg -n --hidden -g 'dag.json' -g 'decomposition-v*.json' -g '*.lean' 'p02_es_177ebb5a_tb_(strip_coefficient_limit|fixed_form|eval_bound|periodic_strip_bound)' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_tb_decomposition_types.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/Polynomial`
- `/tmp/p02_tb_decomposition_types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected project definitions match the local elaboration environment; local mathlib has the pinned revision and clean Git status. IsEichlerIntegral is coefficientwise differentiation, and binaryFormRepSL uses column substitution, so T^N substitutes (X,Y) ↦ (X,NX+Y). Mathlib supplies homogeneous support and evaluation formulas, exponential decay and integrability, translation action formulas, and the exact eventual-bound criterion. The polynomial searches found no relevant translation-fixed classification; the evaluation searches found no matching homogeneous coefficient-bound estimate. All four proposed types elaborate after import Submission. The proposed names have no match in the current DAG or recorded decompositions. Transitive axiom checks for binaryFormRepSL_apply_coe, modular_T_zpow_smul, isBoundedAtImInfty_iff, and tendsto_pow_mul_exp_neg_atTop_nhds_zero report only propext, Classical.choice, and Quot.sound. These checks validate interfaces and library evidence, not acceptance of the proposed child proofs.
