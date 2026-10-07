# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_parabolic-a1`
- Child DAG node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N,n,f,F and the asserted Eichler-integral hypothesis, and fix σ∈SL₂(ℤ). Write V=BinaryForm ℂ n, R=binaryFormRepSL ℂ n σ, L(z)=(zX+Y)^n, H(z)=F(σz), and u(z)=j(σ,z)^(−(n+2))f(σz). Apply the sibling scaled_cusp_decay theorem to N,n,f,σ. It supplies a>0, C≥0, and Y such that |u(x+it)|≤C exp(−at) whenever t≥Y and t>0.
2. Every polynomial in V has a unique expansion in the n+1 monomials X^rY^(n−r), for 0≤r≤n. All coefficients outside total degree n vanish. Use these n+1 coefficients to identify V with ℂ^(n+1), and give it the maximum coefficient norm. This is a complete normed vector space because a Cauchy sequence has a limit in each of its finitely many complete complex coordinates; the resulting coordinates define a homogeneous polynomial of degree n. The fixed linear map R is given in these coordinates by a finite matrix. If K is the maximum of its absolute row sums, the triangle inequality gives ‖RP‖≤K‖P‖ for every P∈V.
3. The Eichler-integral hypothesis says that each coefficient function of F has complex derivative f(w) times the corresponding coefficient of L(w), at every w∈ℍ. The Möbius function w=σz has derivative j(σ,z)^(−2), since det σ=1. The coefficientwise chain rule therefore gives the derivative of the d-coefficient of H as f(σz)j(σ,z)^(−2) coeff_d(L(σz)). The existing identity R L(z)=j(σ,z)^n L(σz), together with j(σ,z)≠0, rewrites this derivative as u(z) coeff_d(R L(z)). Thus H'(z)=u(z)R L(z) in the finite coefficient space. These derivatives are continuous: u is holomorphic and R L(z) has polynomial coefficient functions. The use of ofComplex in IsEichlerIntegral causes no change locally, because all points and their nearby images lie in the open upper half-plane.
4. Fix B>0 and take t≥1 and |x|≤B. The r-th coefficient of L(x+it) is binomial(n,r)(x+it)^r. Since |x+it|≤B+t≤(B+1)(1+t), and binomial(n,r)≤2^n, its absolute value is at most D_B(1+t)^n, where D_B=2^n(B+1)^n. This also covers n=0. Put Y₀=max(1,Y) and C_B=CKD_B. Steps 1–3 give ‖H'(x+it)‖≤C_B(1+t)^n exp(−at) whenever |x|≤B and t≥Y₀.
5. The nonnegative integral J=∫₀^∞(1+s)^n exp(−as) ds is finite. Indeed, expand (1+s)^n by the binomial theorem. For every integer r≥0, the inequality exp(as)≥(as)^(r+1)/(r+1)! for s>0 implies s^r exp(−as)≤(r+1)!/(a^(r+1)s), so the boundary term tends to zero at infinity. Integration of exp(−as) gives 1/a, and integration by parts on finite intervals, followed by this boundary limit and induction on r, gives ∫₀^∞s^r exp(−as) ds=r!/a^(r+1). Consequently J is the finite sum Σ_{r=0}^n binomial(n,r)r!/a^(r+1). The same boundary estimate, applied to the polynomial expansion, shows (1+y)^n exp(−ay)→0.
6. For y≥Y₀, substitution t=y+s and 1+y+s≤(1+y)(1+s) show that ∫_y^∞(1+t)^n exp(−at) dt≤J(1+y)^n exp(−ay). On the imaginary ray, the real derivative of H(it) is iH'(it). Applying the fundamental theorem of calculus to its finitely many continuously differentiable coefficients and using step 4 with B=1 therefore gives, for v≥y≥Y₀, ‖H(iv)−H(iy)‖≤C_1 J(1+y)^n exp(−ay). The right side tends to zero, so H(iy) is Cauchy as y→∞. Completeness from step 2 supplies a limit A∈V.
7. Fix any real x and choose B>|x| with B>0. For y≥Y₀, the horizontal segment from iy to x+iy lies in |Re z|≤B. Integrating H' along this segment gives ‖H(x+iy)−H(iy)‖≤|x|C_B(1+y)^n exp(−ay), which tends to zero by step 5. Since H(iy)→A, it follows that H(x+iy)→A. This proves that the limit is independent of x without any equivariance assumption on F.
8. Every degree-n coefficient is a continuous coordinate in the norm of step 2, so its limit is the corresponding coefficient of A. Every coefficient of a different total degree is identically zero for H and A. Thus convergence holds for every d:Fin 2→₀ℕ. Finally, y>0 holds eventually along Filter.atTop, and on that eventual set UpperHalfPlane.ofComplex(x+iy) is precisely the upper-half-plane point x+iy. Replacing a function by an eventually equal function preserves its limit, proving the exact Lean proposition.

## Key steps

1. Obtain exponential decay of the scaled cusp form from scaled_cusp_decay.
2. Identify homogeneous binary forms with their finite coefficient space and bound the fixed representation operator.
3. Differentiate F(σz) coefficientwise and use linePow covariance to obtain H'=uρ(σ)L.
4. Bound the derivative on each bounded horizontal strip by a polynomial times an exponential.
5. Prove integrability and vanishing of the exponential tails.
6. Use vertical integration and completeness to construct a limiting polynomial on the imaginary ray.
7. Use horizontal integration to show every fixed real part has the same limit.
8. Pass to all coefficients and justify the eventual ofComplex representation.

## Reference use

### local-project

Queries:
- `IsEichlerIntegral|IsEquivariantPrimitiveWith|IsParabolicCocycle|eichlerShimuraMap_injective|exp_decay_atImInfty`
- `isCusp|isZeroAt|zero_at|conj|slash|normal|strictPeriods`
- `trace.*(sq|\^ 2)|parabolic.*conjug|conjug.*parabolic|exists.*(T \^|T\^)`
- `coe_T_zpow|T_zpow|neg.*smul|smul.*neg|def ofComplex|ofComplex_apply`
- `rg -n 'p02_es_177ebb5a_pp_(scaled_cusp_decay|primitive_cusp_limit|integral_parabolic_normal_form)' Submission.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes`
- `git -C .lake/packages/mathlib status --short`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `cmp Definitions/Def_HeckeEis_EichlerIntegral.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `cmp Definitions/Def_HeckeEis_BinaryFormRep.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `cmp Definitions/Def_Gamma0CoeffCohomology.lean .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_177ebb5a_pp_typecheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/tmp/p02_177ebb5a_pp_typecheck.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The installed mathlib matches that revision and has clean Git status; the three relevant project definition files match the snapshot byte-for-byte. Existing infrastructure supplies sub_eq_cocycle, binaryFormRepSL_linePow, jFactor_ne_zero, Gamma_normal, ModularGroup_T_pow_mem_Gamma, and cusp vanishing after slash. QExpansion.lean supplies exponential decay from positive periodicity, holomorphy, boundedness, and vanishing at imaginary infinity. The searched matrix, modular-form, and project-definition sources contain no matching integral conjugacy theorem covering every trace-squared-four matrix. The proposed identifiers have no matches in Submission or the DAG metadata. All three exact propositions elaborate after import Submission under Lean 4.33.1; additional checked equalities verify matrix multiplication and matrix negation for the inferred special-linear-group instances. Transitive axiom checks for the seven inspected reusable lemmas report only propext, Classical.choice, and Quot.sound. These checks validate the interfaces and reference reuse, not acceptance of new theorem proofs.
