# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_sum_zero-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_sum_zero-a1.two_torsion_four_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix G and T satisfying the hypotheses. Since 2 • 0 = 0, the membership characterization gives 0 ∈ T. Every x ∈ T satisfies x + x = 2 • x = 0, so −x = x. If x and y belong to T, then 2 • (x + y) = 2 • x + 2 • y = 0, and consequently x + y belongs to T.
2. Choose U ∈ T with U ≠ 0. Such an element exists because otherwise T would be contained in {0} and have cardinality at most one, contradicting its cardinality four. Next choose V ∈ T with V ≠ 0 and V ≠ U. Otherwise T would be contained in {0, U}, whose cardinality is two, again contradicting its cardinality four.
3. By step 1, U + V belongs to T. It is nonzero: if U + V = 0, then V = −U = U, contrary to step 2. It differs from U, because U + V = U would imply V = 0 by cancellation. It differs from V, because U + V = V would imply U = 0 by cancellation. Together with step 2, these facts show that 0, U, V and U + V are pairwise distinct.
4. Let A = {0, U, V, U + V}. Steps 1–3 give A ⊆ T and cardinality A = 4. Since T also has cardinality four, A = T: a proper inclusion of finite sets would force a strict inequality of cardinalities.
5. Enumerating the four distinct elements and using associativity and commutativity, the sum of T is 0 + U + V + (U + V) = (U + U) + (V + V) = 2 • U + 2 • V. Both scalar multiples vanish by the membership characterization and U, V ∈ T. Thus the sum of T is zero.

## Key steps

1. Show that T contains zero, is closed under addition, and each element equals its negative.
2. Use cardinality four to choose distinct nonzero elements U and V.
3. Show that 0, U, V and U + V are four distinct elements of T.
4. Use equal finite cardinalities to prove that these elements exhaust T.
5. Regroup their sum as 2 • U + 2 • V and conclude that it is zero.

## Reference use

### local-project

Queries:
- `sum_involution|sum.*eq.*neg|sum.*filter.*(neg|two)|sum.*(torsion|orderOf)|sum.*eq_zero`
- `instance.*(AddCommGroup|AddGroup)|nsmul :=|nsmulBinRec|deriving.*DecidableEq`
- `sum.*(torsion|card_four|card.*4|two_nsmul)|sum_eq_sum.*(filter|neg)|sum.*filter.*two`
- `prod.*(invol|eq_one|card)|card.*4|Klein`
- `p03_eds_negation_fixed_sum_68cf3476_d5|p03_eds_two_torsion_four_sum_68cf3476_d5`
- `python3 /tmp/p03_eds_sum_decomposition_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/GroupTheory/FiniteAbelian`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p03_eds_sum_split_ngfjxqfk/ChildTypes.lean`
- `/tmp/p03_eds_sum_split_ngfjxqfk/ChildTypes.lean.log`
- `/tmp/p03_eds_sum_split_ngfjxqfk/InstancesAxioms.lean.log`
- `/tmp/p03_eds_sum_split_ngfjxqfk/TargetAbsence.lean`
- `/tmp/p03_eds_sum_split_ngfjxqfk/receipt.json`

The snapshot and compiler dependencies matched their pinned revisions and were clean: project 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Finset/Basic.lean supplies Finset.sum_involution through to_additive; Affine/Point.lean supplies decidable equality and the canonical additive commutative point group. Targeted searches found no matching four-element two-torsion sum theorem in the searched modules. Both proposed exact types elaborated after import Submission in a disposable copy of proof base 3faf7ece669acd01820d0d4ce378f0b98a1944a6. Lean confirmed the point-group instance and definitionally checked its natural scalar multiplication against nsmulBinRec. The inspected library declarations use only propext, Classical.choice and Quot.sound, or no axioms. Neither proposed name occurs in the ten local problem DAGs or the imported environment. The matching header policy had digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; only lines 10 and 11 were omitted in the disposable compiler copy, and Lean checked all 37 targets absent. The receipt records exact omitted lines, original/build hashes and byte-exact reversibility. Repository files remained unchanged. These are interface diagnostics, not comparator acceptance of child proofs.
