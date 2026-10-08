# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.finite_inverse_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. For j ≥ i, let A_ij be the image of r_ij in X_i. Each A_ij is nonempty. Coherence gives A_ik ⊆ A_ij whenever i ≤ j ≤ k.
2. For each fixed i, choose an index at which the cardinality of A_ij is minimal among j ≥ i. Every later image is contained in that image and has at least its minimal cardinality, so finiteness makes the images equal. Thus the intersection X_i∞ of all A_ij is nonempty and equals every sufficiently late image.
3. The adjacent map r_i,(i+1) sends X_(i+1)∞ into X_i∞: for any j ≥ i+1, coherence sends the image A_(i+1),j into A_ij, and membership for j = i is automatic. It is surjective on these stable subsets. Indeed, choose j beyond stabilization at both i and i+1. For x ∈ X_i∞ = A_ij choose z ∈ X_j with r_ij(z) = x. Then y = r_(i+1),j(z) belongs to X_(i+1)∞, and coherence gives r_i,(i+1)(y) = x.
4. Choose x_0 ∈ X_0∞ and recursively choose x_(i+1) ∈ X_(i+1)∞ mapping to x_i under the adjacent map. Step 3 supplies a lift at every stage.
5. For any i ≤ j, induction on j−i proves r_ij(x_j) = x_i. The base case is the identity transition. The induction step follows by factoring through j−1 and using the adjacent equality and coherence. Hence the chosen family satisfies every required compatibility.

## Key steps

1. Form the decreasing nonempty transition images at each level.
2. Use finiteness to obtain nonempty stable images.
3. Prove that adjacent maps between stable images are surjective.
4. Choose successive lifts and deduce all-pairs compatibility.

## Reference use

### local-project

Queries:
- `rg -n 'modularCyclotomicCharacter|theorem spec|theorem unique|TODO|IsAdicComplete|exists_pow_inf_eq_pow_smul|iInf_pow_smul_eq_bot_of_isLocalRing|trace_eq_matrix_trace' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Filtration.lean .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `rg -n 'Chebotarev|chebotarev|FrobeniusDensity' project/Definitions mathlib/Mathlib/NumberTheory mathlib/Mathlib/RingTheory`
- `rg -n 'smul_eq_mul|theorem sub_apply|theorem smul_apply' mathlib/Mathlib/Algebra/Algebra/Operations.lean mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean`
- `python3 .humanize/decomposition-interface-fresh-tdjulkl6/finish.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_GaloisRep_Adic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Filtration.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Algebra/Operations.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Module/LinearMap/End.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Frobenius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/Complex/Polynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/decomposition-interface-fresh-tdjulkl6/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/decomposition-interface-fresh-tdjulkl6/name-reservations.json`

The snapshot matches project commit 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d; both tracked trees are clean. Relative search paths above use the stated snapshot root. The definitions confirm the exact continuity, trace, LiesOverPrime and arithmetic IsFrobeniusAt predicates. Mathlib supplies finite cyclotomic characters, adic completeness, Artin–Rees, finite-module separation and matrix trace identification; cyclotomic compatibility is explicitly a TODO and is proved below. The Chebotarev/FrobeniusDensity search returned no matches in its three searched subtrees. RingTheory/Frobenius.lean supplies Frobenius at a given prime, not the required prime-distribution assertion. Fresh disposable checks passed for all eight unchanged types after both import Submission and import Challenge, including composition, pointwise linear-map operations and ideal-action probes. Inspected type and supporting-declaration axiom dependencies are subsets of propext, Classical.choice and Quot.sound. The report records the exact policy-authorized omissions, a successful eight-target absence probe, original/build hashes and unchanged protected files. These are interface diagnostics, not comparator acceptance or accepted child proofs.
