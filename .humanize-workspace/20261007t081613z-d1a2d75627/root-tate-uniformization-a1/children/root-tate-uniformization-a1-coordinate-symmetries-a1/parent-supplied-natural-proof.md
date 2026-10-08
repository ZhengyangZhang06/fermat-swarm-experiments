# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_uniformization-a1`
- Child DAG node: `root.tate_uniformization-a1.coordinate_symmetries-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write A(z) = z/(1−z)^2 and B(z) = z^2/(1−z)^3, and retain Q and C from the statement. Norm preservation of the algebra map gives Q ≠ 0. Fix a unit u outside Q^ℤ. Every Q^n u is nonzero and differs from one, since Q^n u = 1 would give u = Q^(−n).

2. The nonzero elements Qu and u⁻¹ also lie outside Q^ℤ: equations Qu = Q^m and u⁻¹ = Q^m would respectively imply u = Q^(m−1) and u = Q^(−m). An F-algebra automorphism σ fixes Q and C. If σ(u) = Q^m, applying σ⁻¹ gives u = Q^m, so σ(u) is likewise outside Q^ℤ. Regard these nonzero elements as units. The sibling bilateral_summability theorem applies with the given F, Ω and q to each of them. Therefore all A- and B-families used below are summable in Ω, and their sums may be reindexed and added.

3. For every integer n, Q^n(Qu) = Q^(n+1)u. Translation n ↦ n+1 is a bijection of ℤ, so reindexing gives Σ_n A(Q^n Qu) = Σ_n A(Q^n u) and the analogous equality for B. Subtracting 2C and adding C respectively proves X(Qu)=X(u) and Y(Qu)=Y(u).

4. For nonzero z ≠ 1, the identity 1−z⁻¹ = −(1−z)/z gives A(z⁻¹)=A(z). It also gives B(z⁻¹)=−z/(1−z)^3=−B(z)−A(z). Reindex the series at u⁻¹ by n ↦ −n and use Q^(−n)u⁻¹=(Q^n u)⁻¹. Thus its A-sum equals the A-sum at u, and its B-sum equals minus the B-sum at u minus the A-sum at u. If these latter sums are S_A and S_B, then X(u⁻¹)=S_A−2C=X(u), while Y(u⁻¹)=−S_B−S_A+C=−(S_B+C)−(S_A−2C)=−Y(u)−X(u).

5. Fix an F-algebra automorphism σ. The sibling algebraic_aut_isometry theorem applies with the given complete base, algebraic extension and q, so σ is an isometry and hence continuous. It preserves addition, multiplication, inverses and integer powers, and fixes Q. Consequently σ(A(Q^n u))=A(Q^n σ(u)) and σ(B(Q^n u))=B(Q^n σ(u)) for every n.

6. Apply σ to the convergent nets of finite partial sums of the two series at u. Continuity and step 5 show that their limits are the corresponding sums at σ(u); uniqueness of limits in the normed field Ω identifies these limits. Since σ fixes C and the integer 2, subtracting 2C and adding C gives X(σ(u))=σ(X(u)) and Y(σ(u))=σ(Y(u)). Together with steps 3 and 4, these are all the claimed identities.

## Key steps

1. Check that translation, inversion and algebraic automorphisms preserve the nonkernel domain.
2. Apply bilateral summability to justify all sum manipulations.
3. Reindex by integer translation to prove periodicity.
4. Reindex by negation and use two rational identities to prove inversion formulas.
5. Apply automorphism isometry to obtain continuity.
6. Pass automorphisms through convergent sums and fixed base-field constants.

## Reference use

### local-project

Queries:
- `TateCurve|tateCurve|tateUniformization|LaurentAnalytic|Laurent.*annulus|lambert|Lambert`
- `FiniteDimensional.complete|LinearMap.continuous_of_finiteDimensional`
- `summable_of_norm_bounded|summable_geometric_of_norm_lt_one`
- `theorem Summable.of_norm_bounded|lemma Summable.of_norm_bounded|theorem Summable.of_norm|lemma Summable.of_norm`
- `exists_isWeierstrassFactorization|theorem complete|continuous_of_finiteDimensional|summable_norm_iff|multipliable.*norm|multipliable.*sub|tprod_ne_zero`
- `p03_tu_(lambert_summable|euler_product_powers|bilateral_summable|algebraic_aut_isometry|coordinate_symmetries)_68cf3476`
- `python3 /tmp/p03-tu-decomposition-14v63537/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Summable.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/NumberTheory/TsumDivisorsAntidiagonal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p03-tu-decomposition-14v63537/result.json`
- `/tmp/p03-tu-decomposition-14v63537/ExtraType.lean.log`
- `/tmp/p03-tu-decomposition-14v63537/LibraryEvidenceV2.lean.log`

The snapshot pins project 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. It supplies geometric-series comparison, finite-dimensional completeness and continuity, induced norms, infinite-product convergence infrastructure, and formal Weierstrass preparation. The Lambert-series search found divisor-sum identities, but no matching Tate uniformization or annular Laurent-analysis interface. All five proposed types elaborate after import Submission in a disposable compiler copy. The matching policy digest is 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; only lines 10 and 11 were omitted, after Lean confirmed all 37 targets absent. The reversible original/build hashes are dd8891addb75e48583885c932518af8bc6d34438aec4e3ccd76ce6aa765e423f and 81502485ae6796527a5c4e210837b198322b438244a2f58054b94b98aef9dda9. Pinned sources and dependencies were clean; the original sources were unchanged. Source searches and all ten local DAGs showed no proposed-name collisions. Induced intermediate-field norms and multiplication were checked. The five type expressions and seven inspected library theorems depend only on propext, Classical.choice and Quot.sound. These are interface diagnostics, not theorem-comparator acceptance.
