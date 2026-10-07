# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.finite_order_support_ascent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the fields, compatible scalar tower and finite separable extension in the statement, and assume the stated finite-support hypothesis on E. Fix f ≠ 0 in L. Finite-dimensionality implies that f and f⁻¹ are algebraic over E: sufficiently many powers are linearly dependent, and dividing a nontrivial dependence by its highest nonzero coefficient gives a monic polynomial. Choose monic polynomials P,Q over E annihilating f and f⁻¹, respectively.

2. Let C be the finite set of nonzero coefficients occurring in P or Q. It is finite because a polynomial has finitely many nonzero coefficients. For each a in C, let S_a be the set of project places v of E over K where ord_v(a) ≠ 0. Every S_a is finite by hypothesis. Hence T = ⋃a∈C S_a is finite.

3. At a project place v, a nonzero element a with nonnegative order lies in its valuation ring. Indeed, choose a uniformizer π and use Place.exists_unit_mul_zpow to write a = uπ^(ord_v(a)); a nonnegative exponent is a natural power of an element of the ring. In particular order zero implies membership. Zero belongs to the ring separately. Therefore, if v is outside T, every coefficient of P and Q belongs to O_v: each nonzero coefficient has order zero there, and zero coefficients require no condition.

4. Every project place w of L over K restricts to a project place v = w.restrict E. This is the existing algebraic restriction construction in Def_AlgebraicCurve_DivisorPushPull.lean; its algebraicity hypothesis follows from finite-dimensionality. Its defining valuation subring is the inverse image of O_w under E → L. Consequently the image of O_v is contained in O_w. The scalar-tower hypothesis ensures that this restriction still contains the given image of K.

5. Suppose v = w.restrict E lies outside T. Map P and Q to polynomials over L. By steps 3–4 all their coefficients belong to O_w, and they remain monic. Their roots are f and f⁻¹. Apply the existing Place.mem_of_eval_monic_eq_zero from Def_AlgebraicCurve_PlacesOverDVR.lean to obtain f ∈ O_w and f⁻¹ ∈ O_w. Equivalently, one may see the integral-root assertion directly: a root z of negative order in a monic equation would, after division by the leading power of z, put 1 in the maximal ideal, since each lower term has positive order. Thus neither of these two roots can have negative order.

6. Since f and f⁻¹ both belong to O_w, f is a unit of O_w, with inverse f⁻¹. The project order of a unit is zero, by Place.ord_coe_unit. Therefore ord_w(f) = 0 whenever w.restrict E is outside T.

7. For each v in T, the fiber {w | w.restrict E = v} is finite by Place.finite_setOf_restrict_eq in Def_AlgebraicCurve_PlacesOverDVR.lean. Its hypotheses are precisely a compatible field tower, finite-dimensionality and separability; it does not assume principal divisors or finite order support upstairs.

8. Step 6 gives {w | ord_w(f) ≠ 0} ⊆ ⋃v∈T {w | w.restrict E = v}. The right side is a finite union of finite sets by steps 2 and 7, and hence is finite. Its subset on the left is finite. Since f was arbitrary and nonzero, this proves the exact assertion.

## Key steps

1. Choose monic equations over E for f and f⁻¹.
2. Take the finite union of the downstairs order supports of their nonzero coefficients.
3. Outside that union, place all coefficients in the restricted valuation ring and then in the upstairs ring.
4. Apply integral closedness to put both f and f⁻¹ in the upstairs ring.
5. Conclude that f has order zero outside the fibers over the exceptional set.
6. Use the existing finite-fiber theorem to prove finite support upstairs.

## Reference use

### local-project

Queries:
- `rg -n 'finite_setOf_restrict_eq|inertiaDeg|PushforwardNormFormula|RatFunc' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions`
- `grep -nE 'residueDegree|FiniteResidue|finrank|ord_norm|norm.*ord|finite.*support|finite.*ord|hasPrincipalDivisors|congrEquiv|congr.*ord' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_*.lean`
- `grep -R -nE 'RatFunc|congrEquiv|congrRingEquiv' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions | head -50`
- `grep -R -nE 'norm.*(valuation|intValuation)|valuation.*norm' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/NumberTheory/RamificationInertia`
- `sed -n '165,230p' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `grep -nE 'traceForm_nondegenerate|isIntegral_trace' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Trace/Basic.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Trace/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Norm/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/FieldTheory/Separable.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/CheckTypes.interface-check.log`

The requested rg query failed because rg is unavailable; grep searches were used instead. DivisorClassGroup supplies the exact place, order, divisor and HasPrincipalDivisors definitions and normalized uniformizer factorization. DivisorPushPull supplies restriction, the canonical residue algebra, inertiaDeg, the residue-degree tower identity, and degree_pushforward. PlacesOverDVR supplies the integral-root lemma and finite fibers without assuming HasPrincipalDivisors upstairs. No rational-function transport infrastructure matched the search of project/Definitions, and no valuation-of-norm identity matched the searched mathlib DedekindDomain and RamificationInertia directories. The normalization and localization theorems support the local norm proof. Project HEAD matches 956e8c600d8b95b46948ae5e37b13930b5f3d06b; all nine dependencies are clean at their manifest revisions, including mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Byte-identical copies of the three imported project modules compiled. The audited imported lemmas have only propext, Classical.choice and Quot.sound as transitive axioms. All proposed types and the canonical residue-algebra checks pass under an isolated import-only Submission module containing the exact frozen import. The unchanged original Submission fails on three pre-existing attribute directives referring to unavailable declarations; its failure log is preserved. Thus validation against an unchanged, successfully importing Submission remains an activation gate. No comparator acceptance is claimed.
