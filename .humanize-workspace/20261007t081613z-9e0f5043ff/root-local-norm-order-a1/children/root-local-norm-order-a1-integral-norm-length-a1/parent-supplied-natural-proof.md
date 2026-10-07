# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1`
- Child DAG node: `root.local_norm_order-a1.integral_norm_length-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the tower, v, and nonzero b. Put A = O_v and B = integralClosureAt L v. The ring A is a DVR with fraction field E, hence is Noetherian, integrally closed, and a principal ideal domain. Its canonical map into L is the composite A → E → L and is injective. Consequently L is torsion-free over A. The hypotheses of IsIntegralClosure.finite and IsIntegralClosure.module_free in the pinned Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean hold, so B is a finite free A-module. The canonical map B → L is injective, and the canonical scalar actions form the required towers.

2. Choose a finite A-basis (e_i) of B. Its images in L are E-linearly independent. Indeed, an E-linear relation has finitely many coefficients. Since E is the fraction field of A, choose a common nonzero denominator d ∈ A making all coefficients integral over the coefficient ring in the elementary sense d c_i ∈ A. Multiplying the relation by d gives an A-linear relation between the e_i, using injectivity of B → L. A-linear independence gives d c_i = 0 for every i, and d ≠ 0 in the field E then gives c_i = 0.

3. The same images span L over E. For any z ∈ L, finite-dimensionality supplies a monic equation z^m + ∑_{i<m} c_i z^i = 0 with c_i ∈ E and m ≥ 1. Choose nonzero d ∈ A with d c_i ∈ A for every coefficient. Multiplying the equation by d^m shows that dz satisfies a monic equation over A: the coefficient of (dz)^i is c_i d^(m−i), which belongs to A because it equals (d c_i)d^(m−i−1). Thus dz is integral over A and belongs to B. Expand dz in the A-basis and divide the resulting equality in L by the nonzero image of d. This expresses z as an E-linear combination of the images of the e_i. Steps 2 and 3 therefore give an E-basis of L.

4. Let T : B → B be multiplication by b, regarded as an A-linear endomorphism. Write D for its matrix in the A-basis and δ = det_A(T). Applying A → E to the coefficients of the identities b e_j = ∑_i D_ij e_i shows that the matrix of multiplication by the image of b on the E-vector space L is the entrywise image of D. Determinants commute with this ring map because their defining finite sums and products do. Hence the image of δ in E is the determinant of multiplication by b on L, which equals Algebra.norm E b by Algebra.norm_apply.

5. The image of b in L is nonzero by injectivity. Multiplication by it on L is invertible, with inverse multiplication by its reciprocal. Multiplicativity of determinants shows that its determinant has a multiplicative inverse, and so is nonzero. By step 4 the image of δ is nonzero; therefore δ itself is nonzero.

6. Apply the sibling theorem p06_9e0f5043ff_lno_dvr_determinant_length to the finite free A-module B and T. Step 5 checks its determinant hypothesis. It gives a natural number n with length_A(B/range(T)) = n and v.ord of the image of δ equal to n.

7. The range of multiplication by b is exactly the principal ideal bB: its elements are precisely b y with y ∈ B, and commutativity identifies this set with Ideal.span {b}. The corresponding quotient identification is A-linear for the canonical quotient scalar action. Consequently the first equality from step 6 is length_A(B/bB) = n. Replacing the image of δ by the field norm using step 4 gives the second required equality. Both use the same n, as claimed.

## Key steps

1. Obtain a finite free A-module structure on the integral closure.
2. Extend an A-basis of the integral closure to an E-basis of L by clearing denominators.
3. Compare the two multiplication matrices and their determinants.
4. Use invertibility of multiplication in L to prove the integral determinant is nonzero.
5. Apply the DVR determinant-length theorem and identify the range with bB.

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
