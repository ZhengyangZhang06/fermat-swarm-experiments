# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1`
- Child DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1.crl_horizontal_difference_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all hypotheses. For t≥0 write p(t)=(1+t)^n exp(−at). For every integer r≥0 and t>0, the exponential series gives exp(at)≥(at)^(r+1)/(r+1)!, hence 0≤t^r exp(−at)≤(r+1)!/(a^(r+1)t). Each such moment tends to zero. Expanding (1+t)^n as the finite sum Σ_{r=0}^n binomial(n,r)t^r proves p(t)→0 as t→+∞.
2. Fix an arbitrary real x. Set B=|x|+1, which is positive, and choose C≥0 and Y≥1 from the strip hypothesis for this B. These constants are fixed for the remainder of the proof for this x.
3. Let y≥Y and parameterize the horizontal segment by z(s)=sx+iy for real s∈[0,1]. Its imaginary part is y≥1>0, and |Re z(s)|=|sx|≤|x|<B. Therefore ‖G(z(s))‖≤Cp(y) at every point of the segment. Restriction of the complex derivative to the real parameter s and the chain rule give d/ds H(z(s))=xG(z(s)). The derivative is continuous on [0,1], since G is continuous on the upper half-plane and z maps this interval into that set.
4. Apply the fundamental theorem of calculus on [0,1]. The endpoints are z(0)=iy and z(1)=x+iy, so H(x+iy)−H(iy)=∫₀¹xG(sx+iy)ds. Taking norms and using the pointwise bound from step 3 yields ‖H(x+iy)−H(iy)‖≤∫₀¹|x|‖G(sx+iy)‖ds≤|x|Cp(y). The interval has length one. The calculation uses |x| and therefore covers negative x; for x=0 both sides of the resulting bound are zero.
5. The constant |x|C is finite and nonnegative. By step 1, |x|Cp(y)→0. For all y≥Y the norm of the difference lies between zero and this quantity, so its norm tends to zero by the squeeze theorem. Thus H(x+iy)−H(iy)→0 in ℂ. Since x was arbitrary, the asserted convergence holds for every real x, without assuming that H(iy) itself has a limit.

## Key steps

1. Prove polynomial–exponential decay using the exponential series.
2. For fixed x, choose a strip containing its horizontal segment.
3. Differentiate the horizontal parameterization and verify continuity along the segment.
4. Use FTC to bound the horizontal difference by |x|C times the decaying weight.
5. Apply the squeeze theorem to obtain convergence to zero for every fixed x.

## Reference use

### local-project

Queries:
- `eichlerShimuraMap_injective|primitive.*limit|common_ray_limit|integrable.*exp|tendsto.*exp`
- `integrableOn.*exp|integrable.*mul_exp|tendsto.*pow.*exp|integral_eq_sub_of_hasDerivAt|norm_sub_le_integral|cauchy.*atTop|tendsto.*integrable`
- `tendsto.*[Dd]eriv.*[Ii]ntegrable|[Ii]ntegrable.*[Dd]eriv.*tendsto|tendsto.*integrableOn_Ioi|tendsto.*integral_Ioi`
- `integral_eq_sub_of_hasDerivAt|norm_integral_le_integral_norm`
- `p02_es_177ebb5a_crl_`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_crl_decomposition_checks/Types.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/ExpDecay.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/tmp/p02_crl_decomposition_checks/Types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The project search found the frozen injectivity declaration but no matching primitive-limit or exponential-integrability result. Pinned mathlib supplies exponential asymptotics, exponential integrability, convergence from an integrable derivative, FTC, and integral norm bounds. The installed mathlib revision matches, has no tracked modifications, and the five relevant inspected mathlib files match the snapshot byte-for-byte. Both proposed types successfully elaborated after import Submission. Transitive axiom checks of the seven inspected analysis declarations returned only propext, Classical.choice, and Quot.sound. Neither proposed name was reserved in the DAG. These checks validate the interfaces and library infrastructure, not acceptance of the proposed child proofs.
