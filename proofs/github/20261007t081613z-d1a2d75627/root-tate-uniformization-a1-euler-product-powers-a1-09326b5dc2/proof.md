# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_uniformization-a1`
- Child DAG node: `root.tate_uniformization-a1.euler_product_powers-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put R = ‖q‖ and a_d = 1−q^(d+1). Then 0 ≤ R < 1 and ‖q^(d+1)‖ = R^(d+1) < 1. The ultrametric inequality gives ‖a_d‖ ≤ 1. If ‖a_d‖ < 1, the equation 1 = a_d+q^(d+1) contradicts ‖1‖ = 1. Therefore ‖a_d‖ = 1 and ‖a_d−1‖ = R^(d+1).

2. For every N and every finite set S of indices d ≥ N, prove ‖∏_{d∈S}a_d−1‖ ≤ R^(N+1) by induction on S. The empty product has difference zero. For the induction step use AB−1 = (A−1)B+(B−1), the fact that every finite product B of the a_d has norm one, and the ultrametric inequality. The new factor satisfies ‖a_d−1‖ = R^(d+1) ≤ R^(N+1).

3. Let P_S = ∏_{d∈S}a_d for arbitrary finite S. If S and T both contain {0,…,N−1}, put V = S∪T. Then P_V = P_S P_{V\S}, and V\S contains only indices at least N. Thus ‖P_V−P_S‖ ≤ R^(N+1) by step 2 and ‖P_S‖ = 1. The same estimate holds with T. The ultrametric inequality therefore gives ‖P_S−P_T‖ ≤ R^(N+1).

4. Since R^(N+1) tends to zero, step 3 proves that the net of finite products is Cauchy. Completeness of F supplies its limit P, establishing Multipliable. Every P_S has norm one, so continuity of the norm gives ‖P‖ = 1. Hence P is nonzero, and uniqueness of limits identifies P with the stated tprod.

5. Fix k ∈ ℕ. For every finite S, commutativity gives ∏_{d∈S}a_d^k = P_S^k. The power map x ↦ x^k is continuous, so these finite products tend to P^k. This proves their Multipliable assertion and identifies their tprod with P^k. Finally ‖P^k‖ = ‖P‖^k = 1, including k = 0, so this product is nonzero.

## Key steps

1. Show every Euler factor has norm one and geometrically small difference from one.
2. Bound every finite tail product minus one by a geometric tail bound.
3. Prove that the net of all finite products is Cauchy.
4. Use completeness and continuity of the norm to obtain a nonzero product.
5. Pass natural powers through the finite-product limit.

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
