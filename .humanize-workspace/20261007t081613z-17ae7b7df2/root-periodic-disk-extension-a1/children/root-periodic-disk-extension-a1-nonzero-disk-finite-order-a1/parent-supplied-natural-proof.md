# Parent-supplied natural-language proof

- Parent DAG node: `root.periodic_disk_extension-a1`
- Child DAG node: `root.periodic_disk_extension-a1.nonzero_disk_finite_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix A with the stated hypotheses and choose q*∈D with A(q*)≠0. Since D is open, A is analytic at every v∈D by DifferentiableOn.analyticAt in Mathlib/Analysis/Complex/CauchyIntegral.lean:625. At any such v, either A vanishes identically near v, or its Taylor series has a least nonzero coefficient of degree m. In the latter case factoring out (q−v)ᵐ gives A(q)=(q−v)ᵐb(q) near v, where b is analytic and b(v)≠0. This is precisely the local factorization in AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff, Mathlib/Analysis/Analytic/IsolatedZeros.lean:185. Continuity permits shrinking the neighborhood so that b is nowhere zero. Thus in that neighborhood A can vanish only at v.
2. Let E be the set of v∈D near which A vanishes identically. This set is relatively open: a sufficiently small neighborhood of any point in such a zero neighborhood is again a zero neighborhood. Its complement is also relatively open. Indeed, at v∉E the factorization from step 1 provides a disk on which every point other than v has nonzero A-value and hence is outside E; v itself is outside E by assumption. This disk is disjoint from E.
3. The disk D is convex and therefore connected. Since E and its complement are relatively open and q* is outside E, connectedness forces E to be empty. In particular A does not vanish identically on any neighborhood of zero.
4. Apply step 1 at zero. There exist m∈ℕ and b analytic near zero with b(0)≠0 and A(q)=qᵐb(q) near zero. The exponent is unique: if m<n were two such exponents, cancellation at nonzero q would express the leading factor for m as qⁿ⁻ᵐ times the leading factor for n, and continuity at zero would force the former's nonzero value at zero to be zero. AnalyticAt.analyticOrderAt_eq_natCast in Mathlib/Analysis/Analytic/Order.lean:86 identifies analyticOrderAt A 0 with the finite value m. Thus analyticOrderAt A 0≠⊤. AnalyticAt.analyticOrderNatAt_eq_iff in the same file at line 101 then gives analyticOrderNatAt A 0=m.
5. If A(0)=0, the exponent m cannot be zero, because the factorization with m=0 would give A(0)=b(0)≠0. Therefore m≥1, and hence 1≤analyticOrderNatAt A 0. This proves both conclusions.

## Key steps

1. Use analyticity to obtain the local-zero or finite-factorization alternative.
2. Show that the set of locally zero points is both relatively open and relatively closed.
3. Use connectedness and a nonzero value to exclude every zero germ.
4. Identify the finite factorization exponent with both analytic orders.
5. Use A(0)=0 to exclude exponent zero.

## Reference use

### local-project

Queries:
- `qParam|cuspFunction|analyticOrderAt|periodic_disk_extension|pde_holomorphic_extension|pde_finite_order|pde_decay_zero`
- `removable|differentiableOn|bounded|exists|limUnder`
- `analyticOrderAt_eq_top|eqOn_zero|eqOn_of_preconnected|exists_eventuallyEq_pow|analyticAt`
- `exp_log|exp_eq_exp_iff_exists_int`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/Periodic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/RemovableSingularity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`

The snapshot records project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Periodic.lean supplies the q-parameter norm, inverse, and descent API; its global-periodicity hypotheses must not be confused with the parent's periodicity restricted to the upper half-plane. RemovableSingularity.lean provides bounded removable singularities. CauchyIntegral.lean:625 supplies holomorphic-to-analytic conversion; IsolatedZeros.lean:185 supplies local factorization; Order.lean:86,101 identifies the two orders. Log.lean:41,171 supplies exponential surjectivity onto nonzero complex numbers and its integer-period fibers. FundThmCalculus.lean:1140 supports the segment argument. The search found no matching analytic-extension or analytic-order lemma in Def_ModularCurve_GenusNumerics.lean. Inspected mathematical sources match the installed pinned sources; all nine dependencies were clean and matched their pins. The checked library declarations depend only on propext, Classical.choice, and Quot.sound.
