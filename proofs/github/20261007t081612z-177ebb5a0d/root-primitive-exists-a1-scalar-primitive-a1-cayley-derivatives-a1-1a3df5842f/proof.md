# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_exists-a1.scalar_primitive-a1`
- Child DAG node: `root.primitive_exists-a1.scalar_primitive-a1.cayley_derivatives-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define φ(u)=i(1+u)/(1−u) and ψ(u)=(u−i)/(u+i). If |w|<1, then 1−w≠0, since equality would force w=1 of norm 1.
2. The functions u↦i(1+u) and u↦1−u have ordinary complex derivatives i and −1. The complex quotient rule at w gives HasDerivAt φ [(i(1−w)−i(1+w)(−1))/(1−w)²] w. The numerator equals i[(1−w)+(1+w)]=2i, yielding the first asserted derivative.
3. If Im z>0, then z+i≠0 since its imaginary part is Im z+1>0. Both affine functions u↦u−i and u↦u+i have ordinary complex derivative 1. Their quotient therefore has derivative [(z+i)−(z−i)]/(z+i)²=2i/(z+i)² at z, yielding the second asserted derivative.
4. For this z, let s=z+i and t=1−ψ(z). Calculation over s≠0 gives t=[(z+i)−(z−i)]/s=2i/s. Thus t≠0 and ts=2i. Consequently t²s²=(2i)²≠0, and [2i/t²]·[2i/s²]=(2i)²/(t²s²)=(2i)²/(2i)²=1. This is exactly the asserted derivative-factor identity and completes all three conclusions.

## Key steps

1. Establish the nonzero denominator on the disk and apply the quotient rule to φ.
2. Simplify the forward derivative numerator to 2i.
3. Establish z+i≠0 on the upper half-plane and apply the quotient rule to ψ.
4. Use 1−ψ(z)=2i/(z+i) to prove the derivative-factor product equals one.

## Reference use

### local-project

Queries:
- `rg -n 'isExactOn_ball|cayley|Cayley|isExactOn_upperHalfPlane' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b`
- `grep -R -n -E 'isExactOn_ball|def IsExactOn|cayley|Cayley|isExactOn_upperHalfPlane|upperHalfPlane.*[Pp]rimitive' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex --include='*.lean'`
- `HasDerivAt.div|DifferentiableAt.div`
- `HasDerivAt.comp`
- `HasDerivAt.const_mul`
- `def IsEichlerIntegral|def eichlerShimuraMap|def IsEquivariantPrimitiveWith`
- `p02_es_177ebb5a_sp_cayley_equivalence`
- `p02_es_177ebb5a_sp_cayley_derivatives`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_sp_cayley_interfaces.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-scalar-primitive-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/Submission.lean`
- `/tmp/p02_sp_cayley_interfaces.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The requested rg search could not run because rg is unavailable; grep and Python supplied the local searches. HasPrimitives.lean defines Complex.IsExactOn using ordinary HasDerivAt and provides DifferentiableOn.isExactOn_ball. The searched complex-analysis directory contained no Cayley-transform or upper-half-plane primitive result matching the queries. The derivative files provide the required quotient and chain rules. The project definition confirms the coefficientwise ordinary-derivative context. Neither proposed identifier occurred in Submission, the snapshot, or the current DAG/node metadata. Both exact proposed types elaborated after import Submission under Lean 4.33.1. All installed dependency revisions matched the manifest with clean tracked sources; the four consulted mathlib files and three directly imported project definition files matched the snapshot. Transitive axiom checks for the disk-primitive theorem, IsExactOn, quotient rule, chain rule, constant multiplication rule, and differentiability quotient rule returned only propext, Classical.choice, and Quot.sound. These checks validate interfaces and library infrastructure, not comparator acceptance of new proofs.
