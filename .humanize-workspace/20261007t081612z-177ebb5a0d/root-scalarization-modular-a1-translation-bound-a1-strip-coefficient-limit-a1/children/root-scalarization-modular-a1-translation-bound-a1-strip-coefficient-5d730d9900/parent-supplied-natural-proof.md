# Parent-supplied natural-language proof

- Parent DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1`
- Child DAG node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put w(y)=(1+y)^n exp(−ay) and J=∫_(0,∞)w(s)ds. Apply the polynomial_exponential_tail sibling with n and a, whose hypothesis a>0 is given. It supplies integrability, J≥0, w(y)→0, and ∫_y^t w(s)ds≤Jw(y) for 0≤y≤t.
2. Fix x∈[0,L] and t≥y≥y₀. The curve s↦x+is lies in the open upper half-plane for s∈[y,t], since y₀≥1. By the real chain rule its composition with F has derivative iH(x+is). This derivative is continuous by the hypothesis on H. The real fundamental theorem of calculus therefore gives F(x+it)−F(x+iy)=∫_y^t iH(x+is)ds. Taking absolute values, using |i|=1 and the given derivative bound, gives |F(x+it)−F(x+iy)|≤D∫_y^t w(s)ds≤DJw(y).
3. The nonnegative quantity DJw(y) tends to zero. Given ε>0, choose T≥y₀ such that DJw(s)<ε for every s≥T. For any y,t≥T, order the two heights and apply step 2, using symmetry of the distance if necessary. Thus |F(x+it)−F(x+iy)|<ε. This proves the Cauchy criterion at +∞. Completeness of ℂ supplies a limit b_x of F(x+iy) as y→+∞.
4. With x and y≥y₀ fixed, let t→+∞ in step 2. Continuity of the absolute value and the limit from step 3 yield |F(x+iy)−b_x|≤DJw(y).
5. For y≥y₀, apply the same chain rule and fundamental theorem to s↦F(s+iy) on [0,x]. Its derivative is H(s+iy), so |F(x+iy)−F(iy)|≤∫_0^x D w(y)ds=xD w(y). The right side tends to zero. Both terms on the left have limits by step 3, with x and 0 respectively; 0∈[0,L] since L≥0. Continuity of subtraction and absolute value gives |b_x−b_0|=0, hence b_x=b_0.
6. Set b=b_0. Every z in the stated strip equals x+iy with x=Re z∈[0,L] and y=Im z≥y₀. Substituting b_x=b into step 4 proves the required bound. No step divides by D, J, or L, so their zero cases, including the degenerate strip L=0, are included.

## Key steps

1. Apply the polynomial–exponential tail lemma.
2. Integrate the derivative vertically to obtain the bound DJw(y).
3. Use decay and completeness of ℂ to obtain each vertical limit.
4. Pass to the limit in the vertical estimate.
5. Integrate horizontally and use decay to identify all vertical limits.
6. Apply the common limit estimate at an arbitrary strip point.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|def linePow|abbrev BinaryForm|strip.*limit|coefficient.*limit`
- `integrable.*exp|tendsto.*exp|norm_sub_le_integral|finite_of_degree_eq|coeff.*pow`
- `tendsto_pow_mul_exp_neg_atTop_nhds_zero|tendsto_pow_mul_exp|finite_of_degree_eq|continuous.*coeff|ofComplex.*continuous|continuous.*ofComplex`
- `coeff_eq_zero|mem_homogeneousSubmodule|isHomogeneous_monomial|degree`
- `strip.*limit|limit.*strip|linePow.*(bound|norm)|norm.*linePow`
- `rg -n --hidden -g 'dag.json' -g 'decomposition-v*.json' -g '*handoff*.json' -g '*.lean' 'p02_es_177ebb5a_scl_(linepow_coeff_bound|polynomial_exp_tail|scalar_strip_limit)' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_scl_decomposition_types.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Coeff.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/ExpDecay.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DistLEIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Finsupp/Weight.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis`
- `/tmp/p02_scl_decomposition_types.lean`

Both reference snapshots are clean and match project revision 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib is clean at that revision, and the two relevant project definition files match the snapshot byte-for-byte. IsEichlerIntegral specifies coefficientwise complex derivatives; BinaryForm is the homogeneous polynomial submodule. Mathlib supplies multinomial coefficient formulas, exponential integrability and decay, segment norm estimates, finite degree-coordinate sets, and off-degree coefficient vanishing. The strip-limit/linePow-bound search returned no matches. All three proposed names were absent from the DAG and recorded handoffs/decompositions. All three exact types elaborate after import Submission. Transitive axiom checks for the seven inspected supporting declarations report only propext, Classical.choice, and Quot.sound. These are interface and reference checks, not comparator acceptance of any proposed child proof.
