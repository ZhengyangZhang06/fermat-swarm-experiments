# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1.irreducible_evaluation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data, write R = K[T], A = v.toValuationSubring and e(r) = r(x). Transcendence makes e injective. The irreducible polynomial q is nonzero and not a unit. Hence q does not divide 1: a factorization 1 = q r would make q a unit. The membership criterion applied to e(r) = e(r)/e(1) shows that e(r) belongs to A for every polynomial r. In particular let pi be e(q) with this membership proof. Its image is e(q), and pi is nonzero because q is nonzero and e is injective.
2. Apply the sibling fraction_unit_criterion to pi, numerator q and denominator 1. The required fraction identity follows from e(1) = 1 and the denominator condition was proved in step 1. It gives IsUnit(pi) if and only if q does not divide q. Since q divides itself, pi is not a unit.
3. The polynomial q is prime. To verify this directly, if q does not divide r, the gcd of q and r divides q and r. Irreducibility of q forces that gcd to be a unit, since otherwise it is associated to q and q would divide r. Bezout's identity then gives u q + t r = 1. Multiplying by s shows that q dividing r s forces q to divide s. This proves the prime-divisor property for all products.
4. Consider any factorization pi = y z in A. Apply the membership criterion to the images of y and z to choose a,b,c,t in R with q dividing neither b nor t, y = e(a)/e(b), and z = e(c)/e(t). Both b and t are nonzero because q divides zero, so both denominator evaluations are nonzero by injectivity of e.
5. The factorization in F reads e(q) = (e(a)/e(b))(e(c)/e(t)). Multiplying by e(b)e(t) gives e(a c) = e(q b t). Injectivity of e yields a c = q b t.
6. Suppose q divided both a and c. Write a = q a1 and c = q c1. The identity in step 5 becomes q(q a1 c1) = q(b t). Since R is a domain and q is nonzero, cancellation gives q a1 c1 = b t. Thus q divides b t. Primality from step 3 forces q to divide b or t, contradicting the chosen representations. Consequently q does not divide a or q does not divide c.
7. In the first case, apply fraction_unit_criterion to y with its representation a/b and denominator condition to obtain that y is a unit. In the second case, apply that criterion to z with its representation c/t to obtain that z is a unit. Every factorization of pi therefore has a unit factor. Together with step 2 this proves Irreducible(pi). The element pi constructed in step 1, its stated image, and this irreducibility give the required existential conclusion.

## Key steps

1. Use denominator 1 to place every polynomial evaluation in A and construct pi mapping to q(x).
2. Apply the sibling unit criterion to q/1 to prove that pi is a nonunit.
3. Establish the prime-divisor property of q by the gcd and Bezout argument.
4. Represent both factors of pi by permitted fractions and derive ac = qbt.
5. Exclude q dividing both numerators by cancellation and primality.
6. Apply the sibling unit criterion to obtain a unit factor, proving irreducibility.

## Reference use

### local-project

Queries:
- `ord_coe_irreducible|ord_coe_unit|structure Place|def ord|isUnit_iff|theorem ord`
- `aeval_injective|transcendental_iff_injective|theorem.*isUnit.*inv|isUnit_iff.*inv|inv_mem.*isUnit`
- `theorem Irreducible.prime|lemma Irreducible.prime`
- `p06_9e0f5043ff_fno_fraction_isunit|p06_9e0f5043ff_fno_irreducible_aeval|ord.*aeval|aeval.*ord|Irreducible.*aeval|aeval.*Irreducible`
- `p06_9e0f5043ff_fno_fraction_isunit|p06_9e0f5043ff_fno_irreducible_aeval`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Prime/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-654f5e977f/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-654f5e977f/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-654f5e977f/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-654f5e977f/decomposition-typecheck/provenance-check.json`

The snapshot supplies Place.ord_coe_unit, Place.ord_coe_irreducible, transcendental_iff_injective, and Irreducible.prime. The searched snapshot sources contained no matching evaluation-order theorem or proposed-name collision; neither proposed identifier is reserved in the inspected DAG. Both snapshot revisions and all nine dependencies match their manifests and have clean tracked files. Both proposed types elaborate without warnings against the existing isolated import-only Submission interface; definitional checks confirm canonical valuation-subring multiplication. Audited supporting declarations use only propext, Classical.choice, and Quot.sound. However, actual Submission.lean still fails on three pre-existing unknown attribute targets: AlgebraicCurve.IsCurveOver.instNontrivialKaehler, AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply, and AlgebraicCurve.SemilinearAut.coe_torsion_smul. Actual import validation remains required before activation; interface checks are not comparator acceptance.
