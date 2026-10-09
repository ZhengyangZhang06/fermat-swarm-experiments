# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.primitive_parabolic-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write ρ also for the representation of SL₂(ℤ) on V, and put L(z)=(zX+Y)^n. The coefficient derivatives asserted by IsEichlerIntegral imply coefficientwise holomorphy of F on ℍ. For c(γ)=hF.cocycle γ, the constant-defect hypothesis gives F(γz)−ρ(γ)F(z)=c(γ) for every z: evaluate its constant at i to identify it with the frozen cocycle definition.
2. Fix σ∈SL₂(ℤ). Put u(z)=j(σ,z)^(-(n+2))f(σz). The denominator is nonzero on ℍ, so u is holomorphic. Let T=(1 1;0 1). Reduction modulo N has normal kernel Γ(N), which contains T^N and is contained in Γ₀(N). Hence σT^Nσ⁻¹∈Γ. The slash composition identity, obtained from j(αβ,z)=j(α,βz)j(β,z), shows u(z+N)=u(z). Since N>0, the conjugate σT^Nσ⁻¹ is noncentral parabolic and fixes σ∞. Thus σ∞ is a cusp of Γ, and the cusp-form condition says u tends to zero at imaginary infinity uniformly in the real part.
3. This implies an exponential bound |u(x+iy)|≤C exp(−ay), for all x and all sufficiently large y, with C>0 and a=2π/N>0. Indeed, q=exp(2πiz/N) identifies points differing by integer multiples of N and maps ℍ onto the punctured unit disk. Local logarithms and periodicity descend u to a holomorphic function U(q). Uniform vanishing gives U(q)→0 at zero. The removable-singularity theorem extends U holomorphically with U(0)=0. Its local power series therefore gives U(q)=qV(q), where V is holomorphic near zero and bounded on a sufficiently small closed disk. This proves the bound. The same conclusion with these hypotheses is UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty in Mathlib/NumberTheory/ModularForms/QExpansion.lean.
4. Define G(z)=ρ(σ⁻¹)F(σz). The identity ρ(σ)L(z)=j(σ,z)^nL(σz), the derivative (σz)′=j(σ,z)⁻², and the coefficientwise chain rule give G′(z)=u(z)L(z). Give V the maximum norm of its coefficients in X^rY^{n-r}. It is complete, being a finite product of copies of ℂ. For each B>0, the binomial expansion bounds the coefficients of L(x+it) by D_B(1+t)^n when |x|≤B and t≥1. Thus, above some Y≥1, ‖G′(x+it)‖≤C_B(1+t)^n exp(−at).
5. Integrating this bound on vertical segments shows that G(x+iy) has a limit on each vertical ray. More explicitly, with J=∫₀^∞(1+s)^n exp(−as) ds, the tail integral is at most J(1+y)^n exp(−ay), because 1+y+s≤(1+y)(1+s). The integral J is finite: expand the polynomial and integrate each s^r exp(−as) by parts, obtaining r!/a^(r+1). The needed boundary limits follow from exp(as)≥(as)^(r+1)/(r+1)!, which implies s^r exp(−as)→0. Completeness now supplies each ray limit and the uniform tail bound. For two fixed real parts x,x′, horizontal integration gives ‖G(x+iy)−G(x′+iy)‖≤|x−x′|C_B(1+y)^n exp(−ay) for a B containing both. This tends to zero by the same exponential estimate. Hence all ray limits coincide in a single polynomial A∈V.
6. Now fix γ∈Γ with tr(γ)^2=4. Its integer trace is 2ε for ε∈{1,−1}. The determinant-one characteristic polynomial is (t−ε)^2, so γ−εI has a nonzero rational kernel vector. Clear denominators and divide by the greatest common divisor to obtain a primitive integral eigenvector (p,q). Bézout supplies r,s with ps−qr=1. The matrix σ with columns (p,q),(r,s) belongs to SL₂(ℤ), and σ⁻¹γσ has first column (ε,0). Its determinant forces its lower-right entry to be ε, so it equals εT^m for some integer m. This also covers γ=±I, for which σ=I and m=0 may be chosen.
7. Apply steps 2–5 to this σ and write δ=εT^m. Its action on ℍ is z↦z+m. Applying ρ(σ⁻¹) to the constant-defect formula for γ at σz gives ρ(σ⁻¹)c(γ)=G(z+m)−ρ(δ)G(z). Set z=iy and let y tend to infinity. Both G-values tend to A. Every linear operator on the finite-dimensional coefficient space is continuous, so ρ(σ⁻¹)c(γ)=A−ρ(δ)A. Multiplying by ρ(σ) and using γ=σδσ⁻¹ yields c(γ)=ρ(σ)A−ρ(γ)ρ(σ)A=(ρ(γ)−1)(−ρ(σ)A).
8. The explicit vector −ρ(σ)A witnesses membership in the required linear-map range. The argument applies to every γ tested by the trace-squared predicate, including trace −2 and the central cases. Therefore hF.cocycle satisfies the exact IsParabolicCocycle predicate.

## Key steps

1. Identify the frozen cocycle with the constant defect at every point.
2. Obtain positive-period cusp coordinates and exponential decay after any integral scaling matrix.
3. Transform the primitive and prove its derivative is the slashed cusp form times linePow.
4. Use integrable exponential tails and horizontal comparison to obtain a common limiting polynomial.
5. Conjugate every trace-squared-four matrix to εT^m.
6. Take limits in the defect identity and exhibit the required range witness.

## Reference use

### local-project

Queries:
- `rg --files --hidden -g AGENTS.md -g Submission.lean -g lakefile.lean -g lake-manifest.json -g lean-toolchain -g '*dag*' -g '*decomposition*' -g '*state*' -g '!**/.git/**' -g '!**/node_modules/**' .humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d .`
- `IsEichlerIntegral|IsEquivariantPrimitiveWith|coeffH1parMk_eq_zero_iff|p02_es_177ebb5a_`
- `p02_es_177ebb5a_|scalarization`
- `isZero_of_neg_weight|eq_const_of_weight_zero|exp_decay_atImInfty|isBoundedAt_iff|isCusp_SL2Z|isArithmetic_iff_finiteIndex`
- `Gamma0|FiniteIndex`
- `iteratedDeriv|def `
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_es_177ebb5a_typecheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/RemovableSingularity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/NumberTheory/ModularForms/NormTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. rg was unavailable, so searches used grep. The defining files confirm the coefficientwise derivative predicate, constant-defect cocycle, existence branch, trace-squared parabolic test, and quotient by coboundaries. HasPrimitives supplies disk primitives; QExpansion supplies exponential decay; BoundedAtCusp supplies the full scaling-matrix criterion; NormTrace supplies negative-weight vanishing and weight-zero constancy. No scalarization helper matched in the searched P2M directory, and no proposed identifier matched the searched declarations or current DAG, which contains only the root. The six transitive project definition files matched the snapshot; all installed dependencies matched their pinned revisions with clean tracked sources. All five proposed types elaborated under Lean 4.33.1 with only import Submission. Their elaborated modular-form groups use the prescribed mapGL image of Gamma0. Axiom checks of the reused primitive, representation, quotient, decay, cusp, and weight theorems returned only propext, Classical.choice, and Quot.sound. These are interface and library checks, not comparator acceptance of any new proof.
