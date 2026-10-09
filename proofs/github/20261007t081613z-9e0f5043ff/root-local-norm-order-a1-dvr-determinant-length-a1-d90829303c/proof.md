# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the hypotheses and write A = O_v. The project place instances make A a proper DVR with fraction field E. Choose a uniformizer π. Every nonzero a ∈ A is uπ^e for an A-unit u and an integer e ≥ 0. The project lemmas ord_coe_unit, ord_coe_irreducible, and exists_unit_mul_zpow identify e with v.ord(a). In particular, among two nonzero elements of A, the one with smaller order divides the one with larger order.

2. We use length additivity for finite-length modules, as provided by Module.length_eq_add_of_exact in the pinned Mathlib/RingTheory/Length.lean. Its elementary chain argument is as follows. In an exact sequence 0 → U → V → W → 0 with finite-length end terms, concatenate a longest chain in U with inverse images of a longest chain in W to obtain a chain of length ℓ(U)+ℓ(W) in V. Conversely, intersect a chain in V with U and take its images in W. At a strict inclusion at least one resulting inclusion is strict: if both were equal, every element in the larger submodule could have its image lifted from the smaller one, and subtraction would place the difference in their common intersection with U. Thus every chain has at most ℓ(U)+ℓ(W) steps. This proves finiteness and additivity, and consequently additivity for finite direct sums.

3. For every a ∈ ℕ, the quotient A/(π^a) has length a. If a = 0 the quotient is zero. Otherwise its filtration by the images of (π^j), for 0 ≤ j ≤ a, has successive factors (π^j)/(π^(j+1)). Multiplication by π^j induces an isomorphism A/(π) → (π^j)/(π^(j+1)): surjectivity follows from the definition of the principal ideal, and injectivity follows by cancelling the nonzero π^j in the domain A. Each factor is the residue field, which is a simple A-module. Applying step 2 repeatedly gives the asserted length.

4. Choose a finite A-basis of M and let D be the square matrix of T. Its determinant is det(T). If the basis is empty, M is zero, det(T) = 1, and the desired witness is n = 0. Assume henceforth that the matrix has positive size. Its nonzero determinant ensures that it has a nonzero entry.

5. Choose a nonzero entry p having minimum order among the finitely many nonzero entries and move it to the first diagonal position by row and column swaps. By step 1, p divides every entry, including the zero entries. For each subsequent row, subtract the appropriate multiple of the first row to clear the first column. Then subtract appropriate multiples of the first column from the other columns to clear the first row. These operations are invertible over A. The result is block diagonal with blocks p and D′. Its determinant is p det(D′), and is nonzero because every operation multiplies the original determinant by a unit. Since A is a domain, det(D′) is nonzero.

6. Induct on matrix size using step 5. The result is a diagonal matrix with nonzero entries d_i. Write d_i = u_i π^(a_i), with u_i an A-unit and a_i ∈ ℕ. Every row or column operation used has unit determinant, so the determinant order of the original matrix equals the order of the product of the d_i. The normalized order laws therefore give v.ord(det(T)) = ∑_i a_i, with det(T) viewed in E.

7. Right multiplication by an invertible matrix does not change the image of the associated linear map. Left multiplication carries that image by an automorphism of its codomain, and hence induces an isomorphism of cokernels. Thus M/T(M) is A-linearly isomorphic to the cokernel of the diagonal matrix, namely the finite direct sum of A/(d_i). Because u_i is a unit, (d_i) = (π^(a_i)). Steps 2 and 3 give length_A(M/T(M)) = ∑_i a_i.

8. Set n = ∑_i a_i. Step 7 gives the required equality in ℕ∞, and step 6 gives the required equality in ℤ. This proves both conclusions with the same natural number n.

## Key steps

1. Use the normalized DVR order to turn order comparisons into divisibility.
2. Compute the length of A/(π^a) from its residue-field filtration.
3. Diagonalize a nonsingular matrix by invertible row and column operations.
4. Identify its cokernel with a direct sum of principal-power quotients.
5. Compute both determinant order and cokernel length as the sum of the diagonal exponents.

## Reference use

### local-project

Queries:
- `/runtime/bin/rg -n 'fiberEquiv|inertiaDeg|integralClosureAt|ord_norm|norm_ord' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/runtime/bin/rg -n 'norm.*length|length.*norm|det.*length|length.*det' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory`
- `/runtime/bin/rg -n 'length|span|pow|finrank' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `sed -n '120,230p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `sed -n '115,185p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Norm/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/decomposition-typecheck/name-collision-check.json`

The pinned project already supplies integralClosureAt, finite fibers, fiberEquiv, normalized uniformizer orders, and the canonical restriction residue algebra defining inertiaDeg. Mathlib supplies finite free normalization, localization DVRs, length additivity, and scalar-restriction length formulas. No determinant-length or norm-length theorem matched the RingTheory search. Project HEAD and all nine clean dependencies match their recorded revisions; inspected library files and the three project interface files match the snapshot byte-for-byte. The proposed names have no recorded DAG collision. All three proposed types and the residue-algebra, tower-map, and quotient scalar-action checks pass under the inherited isolated import-only Submission shim. Audited imported lemmas use only propext, Classical.choice, and Quot.sound. However, the unchanged authoritative Submission still fails on three pre-existing unavailable attribute targets. Actual Submission import validation remains an activation gate; neither comparator acceptance nor successful authoritative import is claimed.
