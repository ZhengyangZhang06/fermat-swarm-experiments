# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a prime p and a positive integer a, and put q=p^a and R=Z/qZ. We have p≥2, q>0, and p divides q. For any natural integer k, its residue in R is a unit exactly when p does not divide k. Indeed a unit remains a unit under reduction R→Z/pZ, whereas a multiple of p reduces to zero in the nonzero ring Z/pZ. Conversely, if p does not divide k, then gcd(k,p^a)=1: otherwise a prime divisor ℓ of this gcd would divide p^a, hence divide p, hence equal p, contradicting p not dividing k. An integer Bezout identity for k and q reduces to an inverse of k in R. Every residue has a representative k between 0 and q−1, so this criterion covers all residues.
2. A row (r,s) admits x r+y s=1 if and only if r or s is a unit. A unit coordinate gives such coefficients by taking its inverse and setting the other coefficient to zero. If neither coordinate were a unit, their representatives would both be divisible by p by step 1; reduction of x r+y s=1 modulo p would then give 0=1, impossible.
3. Let U be the subtype of rows admitting this equation, and define v~w when a unit u satisfies u v₁=w₁ and u v₂=w₂. Scaling preserves membership in U because coefficients x u⁻¹,y u⁻¹ witness the equation for the scaled row. Unit 1 proves reflexivity, u⁻¹ proves symmetry, and the product of two scaling units proves transitivity. Thus this relation is already an equivalence relation. In particular equality in its Quot is precisely this relation: the equivalence closure used by Quot adds nothing, since each reflexive, symmetric and transitive closure operation preserves the relation.
4. Define F from the disjoint sum R ⊕ {z∈R | z is not a unit} to Quot(~) by F(inl(t))=[(1,t)] and F(inr(z))=[(z,1)]. Both rows belong to U, using coefficients (1,0) and (0,1), respectively.
5. F is surjective. For a representative (r,s), if r is a unit, its inverse scales the row to (1,r⁻¹s). If r is not a unit, step 2 makes s a unit, and its inverse scales the row to (s⁻¹r,1). The latter first coordinate is not a unit, since a unit s⁻¹r would make r=s(s⁻¹r) a product of units. Each quotient class therefore lies in one of the displayed images.
6. F is injective. By step 3, equality of two first-chart classes gives a scaling unit u with u·1=1 and u t=t′, forcing u=1 and t=t′. Equality of two second-chart classes similarly forces u=1 from their second coordinates, then z=z′; the subtype elements agree because their values agree. Equality of a first-chart class and a second-chart class would give u·1=z for a unit u and a nonunit z, a contradiction. Equality in the reverse order reduces to this case by symmetry. These cases exhaust the disjoint sum.
7. The bijection F has an inverse: for each class take its unique preimage, whose existence and uniqueness are steps 5 and 6. The two inverse identities follow from that uniqueness. Its inverse is the asserted equivalence from Quot(~) to R ⊕ {z∈R | z is not a unit}, proving that the type of such equivalences is nonempty.

## Key steps

1. Characterize units modulo p^a by nondivisibility of representatives by p.
2. Reduce a unimodularity equation modulo p to show that a coordinate is a unit.
3. Prove that unit scaling is an equivalence relation, so Quot equality detects precisely unit scaling.
4. Map the two charts to the classes of (1,t) and (z,1).
5. Normalize every unimodular row to prove surjectivity.
6. Use the coordinate equal to 1 and the nonunit restriction to prove injectivity and disjointness.
7. Invert the resulting bijection to obtain the required equivalence.

## Reference use

### local-project

Queries:
- `UnimodularRow|unimodularRow|ProjectiveLine|IsUnit|prime_pow`
- `ProjectiveLine.*(card|equiv)|card.*ProjectiveLine`
- `IsLocalRing.*ZMod|ZMod.*IsLocalRing|isLocalRing.*pow`
- `natCard|card \(|equivFin|natCast_zmod_val|val_lt|val_injective`
- `card_sum|card_congr|card_eq_fintype_card`
- `p10_17ae7b7d_ppr_(unit_chart_equiv|nonunit_card)`
- `python3 .humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/row-card-decomposition-g9q8sg1v/run.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/SetTheory/Cardinal/Finite.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/row-card-decomposition-g9q8sg1v/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/row-card-decomposition-g9q8sg1v/ChildTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/row-card-decomposition-g9q8sg1v/report.json`

The project defines the intended unit-scaling relation, but its ProjectiveLine module is absent from the frozen imports; the children therefore retain an explicit Quot expression. The project search found no matching projective-line chart-equivalence or cardinality theorem. Pinned mathlib provides ZMod.isUnit_natCast_iff_not_dvd_pow, canonical-representative lemmas, Nat.card_congr, Nat.card_sum and Nat.card_zmod. Their inspected transitive axiom sets contain only propext, Classical.choice and Quot.sound. Snapshot revisions and dependency pins were checked clean. Both proposed types elaborate after import Submission in a disposable copy of proof base 1e115a452fbc98bff8aaa6728679030b19690b46; explicit elaboration confirms IsUnit uses the monoid from ZMod.commRing. No proposed-name collision was found. The matching header policy digest was verified, all 56 omitted targets were checked absent by Lean, and exact omitted lines and reversible original/build hashes are recorded in report.json. Original sources remain unchanged. These are decomposition diagnostics, not comparator acceptance.
