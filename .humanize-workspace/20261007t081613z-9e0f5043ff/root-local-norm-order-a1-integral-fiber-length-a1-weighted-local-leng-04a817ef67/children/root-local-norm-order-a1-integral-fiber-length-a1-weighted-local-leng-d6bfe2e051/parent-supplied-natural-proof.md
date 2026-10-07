# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1`
- Child DAG node: `root.local_norm_order-a1.integral_fiber_length-a1.weighted_local_lengths-a1.local_length_multiplicity-a1.localized_residue_factors-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix B, p and q, and set T = q.asIdeal.primeCompl and R = Localization.AtPrime q.asIdeal. Both underlying ideals are maximal: they are nonzero prime ideals of a Dedekind domain. Equality of their underlying ideals implies equality of p and q, by HeightOneSpectrum.asIdeal_injective.

2. First suppose p = q and replace p by q. Let k = B/q.asIdeal, which is a nonzero field because q.asIdeal is maximal. Write bar(a) for the image of a in k. For every s ∈ T, bar(s) is nonzero, since the kernel of B → k is q.asIdeal. Consequently bar(s) is invertible.

3. Define ρ : R → k by ρ(a/s) = bar(a)·bar(s)⁻¹. To check well-definedness, equality a/s = a'/s' supplies t ∈ T with t(as' − a's) = 0. Passing to k and cancelling the nonzero elements bar(t), bar(s), and bar(s') gives bar(a)·bar(s)⁻¹ = bar(a')·bar(s')⁻¹. The formulas for addition and multiplication of fractions show that ρ preserves addition, multiplication, zero, and one. Thus ρ is a ring homomorphism, and it gives k an R-module structure extending its canonical B-module structure.

4. Define Φ : LocalizedModule T k → k by Φ(m/s) = m·bar(s)⁻¹. Equality m/s = m'/s' supplies t ∈ T with bar(t)(bar(s')m − bar(s)m') = 0, so cancellation proves that Φ is well-defined. Its inverse is Ψ(m) = m/1: Φ(Ψ(m)) = m, and Ψ(Φ(m/s)) = m/s because bar(s)(m·bar(s)⁻¹) = m. Fraction addition proves additivity. For a/u ∈ R, the canonical localized action gives (a/u)·(m/s) = (bar(a)m)/(us), whose image under Φ is bar(a)m·bar(u)⁻¹bar(s)⁻¹ = ρ(a/u)Φ(m/s). Hence Φ and Ψ are R-linear inverses.

5. Every nonzero R-submodule W of k equals k. Indeed, choose z ∈ W with z ≠ 0. For any w ∈ k, surjectivity of B → k supplies a ∈ B with bar(a) = wz⁻¹. Stability under the scalar a/1 ∈ R gives w = ρ(a/1)z ∈ W. Since k is nonzero, it is a simple R-module. Transporting this property through Φ proves that LocalizedModule T k is a nonzero simple R-module, establishing the first implication.

6. Now suppose p ≠ q. There is t ∈ p.asIdeal outside q.asIdeal. Otherwise p.asIdeal ≤ q.asIdeal; maximality of p.asIdeal and properness of q.asIdeal would force equality, contradicting step 1 and p ≠ q. This t belongs to T and annihilates B/p.asIdeal: for every representative a ∈ B, ta lies in p.asIdeal. Every element of LocalizedModule T (B/p.asIdeal) is a fraction m/s. Since t·m = 0, the zero-fraction criterion gives m/s = 0. Therefore all elements are equal, proving the second implication and the asserted conjunction.

## Key steps

1. Use maximality and extensionality of height-one primes.
2. When p = q, extend the quotient map to the localization by inverting nonzero denominator classes.
3. Identify the localized residue module with the residue field by mutually inverse R-linear fraction maps.
4. Prove simplicity using a nonzero element and surjectivity of the original quotient map.
5. When p ≠ q, find an annihilator outside q and use the zero-fraction criterion to prove subsingletonness.

## Reference use

### local-project

Queries:
- `length_compositionSeries|length.*[Ll]ocaliz|[Ll]ocaliz.*length|map_exact|localized.*[Qq]uotient|quotient.*[Ll]ocaliz`
- `length.*(sum|localiz)|sum.*length|localiz.*length`
- `HeightOneSpectrum|instance.*[Mm]aximal|theorem.*[Mm]aximal|lemma.*[Mm]aximal`
- `map_injective|map_surjective|linearEquiv|module.*ocalization|[Ll]inearMap.*extendScalars|def map|instance.*Module|mkLinearMap`
- `p06_9e0f5043ff_llm_localized_residue_factors|p06_9e0f5043ff_llm_localized_series_sum`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Length.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Module/LocalizedModule/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Module/LocalizedModule/Exact.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Module/LocalizedModule/Submodule.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Localization`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root/decomposition-typecheck/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-04a817ef67/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-04a817ef67/decomposition-typecheck/ExactnessAxioms.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-04a817ef67/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-weighted-local-leng-04a817ef67/decomposition-typecheck/Submission.frozen-source-check.log`

The snapshot supplies exact localization, preservation of injectivity and surjectivity, localizedQuotientEquiv, length additivity, simple-module length one, zero-module length zero, and maximality and extensionality of height-one primes. The targeted localization-length search in Localization and DedekindDomain found no matching formula. Project revision 956e8c600d8b95b46948ae5e37b13930b5f3d06b and all nine dependencies are clean and match their pins, including mathlib db584cd6d46c92f209a44c0f1c829460d327499d; inspected sources match the snapshot. Both proposed types elaborate after import Submission in the existing import-only interface. Explicit fraction-action checks confirm the canonical localized-module actions, including on successive quotients. Audited library declarations use only propext, Classical.choice, and Quot.sound. No proposed-name collision was found in the DAG, declarations, decompositions, or published handoffs. Authoritative import validation remains blocked: the unchanged frozen Submission source fails on three inherited unknown attribute targets. This must be resolved before child proof work begins; interface checking is not comparator acceptance.
