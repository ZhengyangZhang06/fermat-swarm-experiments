# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1.fraction_unit_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data, write R = K[T], A = v.toValuationSubring, and e(r) = r(x), and identify elements of A with their images in F when computing. Transcendence makes the ring homomorphism e injective: e(r) = 0 forces r = 0, and applying this to a difference proves injectivity. In particular, nonzero polynomials have nonzero evaluations. The irreducible polynomial q is nonzero and not a unit.
2. The polynomial q is prime. Indeed, if q does not divide r, put d = gcd(q,r). Since d divides q and q is irreducible, either d is a unit or d is associated to q. The latter case would imply q divides r, since d divides r. Thus d is a unit. The Euclidean algorithm, followed by multiplication by the inverse of d, gives u q + t r = 1 for some u,t in R. If q divides r s, multiplying this identity by s expresses s as a sum of two multiples of q, so q divides s. Applying this when q does not divide r proves that q dividing r s always forces q to divide r or s.
3. Fix a,b,z satisfying the two final hypotheses. Since q does not divide b and every polynomial divides zero, b is nonzero, hence e(b) is nonzero. First assume q does not divide a. The same reasoning makes e(a) nonzero. By the membership criterion the fraction e(b)/e(a) belongs to A; call the resulting element w. In F the given representation of z yields z w = (e(a)/e(b))(e(b)/e(a)) = 1 and w z = 1. The inclusion A into F is injective and preserves multiplication and one, so both identities hold in A. The pair z,w therefore defines a unit of A with value z.
4. Conversely, assume z is a unit of A and choose its inverse w in A. Applying the membership criterion to the image of w gives c,d in R with q not dividing d and w = e(c)/e(d). Thus d and e(d) are nonzero. The equality z w = 1 in F, together with the representations of z and w, gives e(a)e(c) = e(b)e(d) after multiplication by the nonzero denominator e(b)e(d). Since e is a ring homomorphism and is injective, a c = b d.
5. If q divided a, it would divide a c, hence b d. Primality from step 2 would force q to divide b or d, contradicting the two denominator conditions. Therefore q does not divide a. This proves the reverse implication and hence the stated equivalence.

## Key steps

1. Use transcendence to obtain injectivity of evaluation and nonvanishing of evaluated denominators.
2. Prove primality of q using the polynomial gcd and Bezout identity.
3. For a numerator not divisible by q, use the reversed fraction as an inverse in the valuation ring.
4. For a unit, represent its inverse with a permitted denominator and derive ac = bd by cross multiplication and injectivity.
5. Use primality and the two denominator conditions to exclude q dividing the numerator.

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
