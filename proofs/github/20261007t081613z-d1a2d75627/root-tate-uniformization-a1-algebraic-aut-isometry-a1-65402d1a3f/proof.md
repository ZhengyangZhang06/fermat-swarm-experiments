# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_uniformization-a1`
- Child DAG node: `root.tate_uniformization-a1.algebraic_aut_isometry-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Since 0 < ‖q‖ < 1, q is nonzero and ‖q⁻¹‖ > 1. Thus F is nontrivially normed, with no change to its given norm or field operations.

2. Fix an F-algebra automorphism σ and a nonzero x ∈ Ω. The intermediate field E = F(x), equipped with the norm induced from Ω, is finite-dimensional over F because x is algebraic. The map L : E → Ω obtained by restricting σ is F-linear. The pinned theorem LinearMap.continuous_of_finiteDimensional applies over the complete nontrivially normed field F and proves L continuous. A continuous linear map between normed spaces over such a field is bounded, so there exists a real C > 0 such that ‖L(y)‖ ≤ C‖y‖ for every y ∈ E.

3. Apply this single bound to y = x^n for every positive integer n. Multiplicativity of σ and of the norms yields ‖σ(x)‖^n ≤ C‖x‖^n. Since x ≠ 0, division by ‖x‖^n gives (‖σ(x)‖/‖x‖)^n ≤ C.

4. The ratio in step 3 cannot exceed one. If it were 1+δ with δ > 0, Bernoulli's inequality would give (1+δ)^n ≥ 1+nδ, contradicting the fixed upper bound C for sufficiently large n. Hence ‖σ(x)‖ ≤ ‖x‖. For x = 0 the same inequality follows from σ(0) = 0. This proves the inequality for every automorphism and every x.

5. Apply step 4 to σ⁻¹ at σ(x). It gives ‖x‖ ≤ ‖σ(x)‖, so in fact ‖σ(x)‖ = ‖x‖ for every x.

6. For arbitrary x,y ∈ Ω, additivity of σ and step 5 give dist(σ(x),σ(y)) = ‖σ(x−y)‖ = ‖x−y‖ = dist(x,y). This is precisely the asserted Isometry property.

## Key steps

1. Obtain a nontrivially normed base from q.
2. Restrict an automorphism to the finite-dimensional field F(x).
3. Use finite-dimensional continuity to bound that restriction.
4. Apply the bound to all powers of x to remove the bound constant.
5. Apply the same argument to the inverse automorphism.
6. Translate norm preservation into preservation of distances.

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
