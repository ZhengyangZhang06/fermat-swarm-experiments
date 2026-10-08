# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1.ring_equiv_row_classes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. For each commutative ring A, write U(A) for the subtype of pairs (r,s) satisfying xr+ys=1 for some x,y in A. If u is a unit, multiplying both coordinates by u preserves this condition: x*u^{-1}, y*u^{-1} are witnesses. The relation v~w meaning w=u*v for one unit u is reflexive using 1, symmetric using u^{-1}, and transitive using the product of the two scaling units. Thus the displayed Quot is precisely the quotient by this equivalence relation.
2. Let e:R≃+*S be the given ring isomorphism. Map a row (r,s) to (e(r),e(s)). Applying e to xr+ys=1 gives e(x)e(r)+e(y)e(s)=1, so this is a map U(R)→U(S). Applying e^{-1} defines its inverse; the compositions are identities on both coordinates, and hence on the subtypes.
3. A unit u of R maps to the unit of S whose value is e(u) and whose inverse is e(u^{-1}). The two unit identities follow by applying e to u*u^{-1}=1 and u^{-1}*u=1. If w=u*v in both coordinates, their images satisfy e(w)=e(u)*e(v) in both coordinates. Therefore the row map descends to a function F:P(R)→P(S).
4. The identical construction with e^{-1} descends to G:P(S)→P(R), since it also maps witnesses and units as in steps 2 and 3.
5. For the class of any row (r,s), applying G after F returns the class of (e^{-1}(e(r)),e^{-1}(e(s)))=(r,s). Every quotient element has a representative, so G∘F is the identity. The identities e(e^{-1}(t))=t prove F∘G is the identity in exactly the same way.
6. Thus F and G define an equivalence P(R)≃P(S). Its existence proves the required Nonempty proposition.

## Key steps

1. Verify that simultaneous unit scaling preserves unimodularity and defines an equivalence relation.
2. Transport unimodular rows and their witnesses through the ring isomorphism.
3. Transport units and show that the row map respects the quotient relation.
4. Construct the reverse quotient map using the inverse ring isomorphism.
5. Check both compositions on representatives and obtain the equivalence.

## Reference use

### local-project

Queries:
- `ProjectiveLine|UnimodularRow|unimodularRow|chineseRemainder|primeFactors`
- `chineseRemainder|primeFactors|factorization`
- `(ProjectiveLine|UnimodularRow).*(equiv|Equiv|prod|Pi)|(equiv|Equiv|prod|Pi).*(ProjectiveLine|UnimodularRow)`
- `card_pi|card_congr|finite_quot|finite_quotient`
- `prod_coe_sort|prod_attach|prod_subtype`
- `p10_17ae7b7d_crt_ring_equiv_rows|p10_17ae7b7d_crt_pi_rows`
- `python3 /tmp/p10_crt_split_diagnostic.py`
- `python3 /tmp/p10_crt_refine_types.py`
- `python3 /tmp/p10_crt_parent_assembly.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/ZMod/QuotientRing.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Data/Quot.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/SetTheory/Cardinal/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/crt-split-95f4i2pe/ChildTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/crt-split-95f4i2pe/ParentAssembly.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/crt-split-95f4i2pe/report.json`

The clean snapshots match project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine pinned dependency checkouts were also clean and matched their revisions. The project defines the same unit-scaling quotient and its ring-homomorphism map, but that module is outside the frozen imports, so the child types retain explicit Quot expressions. No corresponding project ring-isomorphism or product-equivalence theorem was found; the targeted search matched only unrelated names sharing header lines. ZMod.equivPi supplies the required CRT isomorphism, while Equivalence.quot_mk_eq_iff, Nat.card_congr, Nat.card_pi and Finset.prod_coe_sort supply quotient equality and cardinality infrastructure. Both proposed names are absent from Submission, the DAG and node metadata. Both final types compiled without warnings after import Submission. Reflexivity checks verified pointwise product-ring multiplication, addition and one, and multiplication of unit values. A conditional Lean proof assembled the exact frozen parent type from these two interfaces. Checked types and library results use only propext, Classical.choice and Quot.sound. The disposable compiler copy followed policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: only lines 10–12 were omitted, and Lean confirmed all 56 targets absent. The report records exact omitted text, reversible original/build hashes and probe evidence. Frozen sources and handoffs were unchanged. These are interface diagnostics, not comparator acceptance of either child proof.
