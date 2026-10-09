# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1.normalized_quotient_rigidity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a commutative ring R and define U and rel as in the statement. The relation rel is reflexive because the unit 1 fixes both coordinates. If u witnesses rel(v,w), multiplying the coordinate equalities by u⁻¹ shows that u⁻¹ witnesses rel(w,v). If u witnesses rel(v,w) and t witnesses rel(w,z), then t u witnesses rel(v,z), since (t u)vᵢ = t(u vᵢ) = t wᵢ = zᵢ for each coordinate i. Hence rel is an equivalence relation on U.
2. Equality Quot.mk rel v = Quot.mk rel w implies that v and w belong to the equivalence closure of rel, by the exactness property of Quot. Every pair in that closure already belongs to rel: a generating pair does by definition, reflexive pairs do by step 1, and the symmetry and transitivity closure operations preserve rel by step 1. Formally this is induction on the four constructors of the equivalence closure. Consequently equality of these quotient representatives supplies a unit u with u v₁ = w₁ and u v₂ = w₂.
3. Assume v and w are normalized and their quotient representatives are equal, and choose u as in step 2. If v₁ = 1 and w₁ = 1, the first scaling equation gives u = 1 as an element of R. The scaling equations then give v₁ = w₁ and v₂ = w₂.
4. If v₁ and w₁ are nonunits and v₂ = w₂ = 1, the second scaling equation gives u = 1 as an element of R. Again both coordinates of v and w are equal.
5. If v₁ = 1 whereas w₁ is a nonunit and w₂ = 1, then u v₁ = w₁ says w₁ = u. This makes w₁ a unit, a contradiction. In the other mixed case, v₁ is a nonunit and v₂ = 1 whereas w₁ = 1. The first scaling equation is u v₁ = 1; multiplying by u⁻¹ gives v₁ = u⁻¹. This makes v₁ a unit, again a contradiction. Thus neither mixed case occurs.
6. The normalization hypotheses give precisely the four cases in steps 3–5. In each possible case the two coordinates agree, so the underlying pairs agree. Subtype extensionality then gives v = w; the proofs of unimodularity do not affect subtype equality. Conversely, if v = w, applying Quot.mk rel to that equality gives equality of their quotient representatives. This proves both directions.

## Key steps

1. Prove that unit scaling is reflexive, symmetric, and transitive.
2. Use Quot exactness and equivalence-closure induction to obtain a single scaling unit from quotient equality.
3. For representatives in the same chart, the coordinate equal to 1 forces the scaling unit to equal 1.
4. Exclude both mixed-chart cases because they would turn a nonunit coordinate into a unit.
5. Apply pair and subtype extensionality, and prove the converse by congruence.

## Reference use

### local-project

Queries:
- `unimodularRow|UnimodularRow|ProjectiveLine`
- `unimodularRow|UnimodularRow|ProjectiveLine|prime_pow|isUnit_iff`
- `prime_power|primePower|chart|nonunit|isUnit_or|IsLocalRing`
- `Quot.eq|eqvGen|EqvGen|exact`
- `eqvGen_iff|EqvGen.*iff|eqvGen_eq|Equivalence.*eqvGen`
- `python3 .humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/unit-charts-split-ky342xt0/run.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Quot.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Logic/Relation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/unit-charts-split-ky342xt0/report.json`

The pinned mathlib supplies ZMod.isUnit_natCast_iff_not_dvd_pow, Quot.eq, and Equivalence.eqvGen_iff. Their transitive axiom checks contain only propext, Classical.choice, and Quot.sound, or no axioms. The inspected project ProjectiveLine file defines unimodular rows and the unit-scaling setoid, but contains no matching prime-power chart theorem; its setoid is absent under the frozen imports, so the proposed types spell out their subtypes and relation. Both exact child types elaborated after import Submission using a disposable copy of proof-base commit 6134a09ac36170885efc4ca0bfae953f03a4e698. The diagnostic verified nine clean pinned dependencies, the required policy digest, reversible omission of precisely lines 10–12, and absence of all 56 omitted targets. Proposed names were absent from the imported environment and active DAG. These are interface diagnostics, not comparator acceptance of any proof.
