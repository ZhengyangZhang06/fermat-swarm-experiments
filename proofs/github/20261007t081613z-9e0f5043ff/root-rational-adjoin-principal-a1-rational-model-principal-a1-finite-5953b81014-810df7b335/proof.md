# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.fraction_subalgebra-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put R = K[T] and e(a) = a(x). Transcendence makes e injective, hence e(b) is nonzero for nonzero b. Irreducibility makes q a nonzero nonunit, so q does not divide 1.
2. If q does not divide b, a greatest common divisor of q and b is a unit: otherwise, as a nonunit divisor of the irreducible q, it is associated to q and forces q to divide b. The Euclidean algorithm in R therefore gives u q + v b = 1. If q divides bt, multiplying this identity by t shows q divides t. Consequently if q divides neither b nor t, it does not divide bt.
3. Let S consist exactly of e(a)/e(b) with q not dividing b. Such b is nonzero, since q divides zero, so e(b) is nonzero. Denominator 1 shows that 0, 1, and each algebraMap K F c = e(C c) belong to S. Negating e(a)/e(b) gives e(-a)/e(b), still in S.
4. For permitted denominators b and t, their product is permitted by step 2, and field arithmetic gives e(a)/e(b) + e(c)/e(t) = e(at+cb)/e(bt) and (e(a)/e(b))(e(c)/e(t)) = e(ac)/e(bt). Thus S is closed under addition and multiplication.
5. These operations make S a subring of F containing the image of K, hence a K-subalgebra A. Its membership characterization is precisely the defining condition for S, as required.

## Key steps

1. Use transcendence to make evaluation injective and irreducibility to obtain the denominator product property.
2. Define the set of fractions with denominator not divisible by q.
3. Verify constants, negation, addition, and multiplication preserve this set.
4. Bundle it as a K-subalgebra with the defining membership equivalence.

## Reference use

### local-project

Queries:
- `structure Place|class Place|extends ValuationSubring|def Place`
- `exists.*[Pp]ow.*[Nn]ot|finiteMultiplicity|multiplicity_eq_zero|theorem multiplicity_mul`
- `aeval_injective|transcendental_iff`
- `class IsPrincipalIdealRing|structure IsPrincipal|class IsPrincipal`
- `principal.*valuation|valuation.*principal|IsPrincipalIdealRing.*ValuationSubring|exists.*ValuationSubring`
- `p06_9e0f5043ff_elp_(fraction_subalgebra|integer_order|principal_ideals_of_order)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Multiplicity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Span.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/Discrete/IsDiscreteValuationRing.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-04071bed87/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-04071bed87/decomposition-typecheck/Submission.frozen-source-check.log`

The snapshot records project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Place requires precisely a valuation subring, containment of constants, properness, and IsPrincipalIdealRing. The inspected library supplies evaluation injectivity from transcendence, finite-multiplicity factorization, multiplicity additivity, and the relevant ring structures. The constructor search in Valuation/Discrete/IsDiscreteValuationRing.lean returned no match; proposed-name searches also returned no collisions. All nine dependency revisions match their pins with clean tracked files, and inspected compiled-context sources match the snapshot. Library axiom checks report only propext, Classical.choice, and Quot.sound. All three proposed types elaborate after import Submission in the existing isolated import-only interface, and inherited multiplication checks pass by definitional equality. The unchanged authoritative Submission still fails on three pre-existing unknown attribute targets; successful authoritative import validation remains required before child activation. These checks are not comparator acceptance.
