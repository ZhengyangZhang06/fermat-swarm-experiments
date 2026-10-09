# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_norm_vanishing-a1`
- Child DAG node: `root.gamma0_norm_vanishing-a1.local_multiplier_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix g, ψ, J and v satisfying the hypotheses, and put m=analyticOrderNatAt g v and λ=ψ′(v). AnalyticAt.analyticOrderNatAt_eq_iff, applied to the analyticity and finite-order hypotheses for g, gives a function b analytic near v with b(v)≠0 and g(z)=(z−v)^m b(z) throughout a neighborhood of v.
2. Expand ψ in a convergent Taylor series at v. Its constant coefficient is ψ(v)=v and its linear coefficient is λ. Removing the constant term and dividing the series by z−v produces an analytic function d near v such that ψ(z)−v=(z−v)d(z) and d(v)=λ. Explicitly, if ψ(v+h)=v+∑_{n≥1}c_n h^n, then d(v+h)=∑_{n≥0}c_{n+1}h^n. The shifted series converges on every smaller disk, including at h=0, and c_1=λ.
3. Choose a sufficiently small disk centered at v on which the factorization of g, the factorization of ψ−v, and the assumed equivariance identity all hold. Continuity of ψ and ψ(v)=v allow this disk to be shrunk further so that ψ(z) lies in the neighborhood where the factorization of g is valid. On this disk, substitution into equivariance gives (z−v)^m d(z)^m b(ψ(z))=J(z)(z−v)^m b(z).
4. For z≠v in this disk, the complex number (z−v)^m is nonzero, including when m=0. Cancel it to obtain d(z)^m b(ψ(z))=J(z)b(z).
5. Each side of this last identity is continuous at v. Taking z→v through the punctured disk gives λ^m b(v)=J(v)b(v), because d(v)=λ and ψ(v)=v. Such a punctured limit exists since every complex disk of positive radius contains points distinct from its center approaching the center. Finally b(v)≠0 permits cancellation, giving λ^m=J(v), exactly the asserted identity.

## Key steps

1. Factor the finite-order germ of g into a power times a nonvanishing analytic factor.
2. Factor ψ(z)−v as (z−v)d(z), with d(v)=ψ′(v).
3. Choose a common neighborhood supporting both factorizations and equivariance.
4. Substitute and cancel the power away from v.
5. Pass to the limit at v and cancel the nonzero leading coefficient.

## Reference use

### local-project

Queries:
- `analyticOrder.*(prod|mul|comp)|eqOn_zero|frequently_eq|isolated`
- `gamma0_norm|cyclic.*norm|elliptic.*order|valence`
- `norm.*prod|prod.*norm|rotation|root.*unity|IsPrimitiveRoot`
- `deriv.*analyticOrderNatAt|analyticOrderNatAt.*deriv|analyticOrder.*multiplier`
- `p10_17ae7b7d_norm_cyclic_product_descent|p10_17ae7b7d_norm_local_multiplier_order`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/OfScalars.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Order.lean supplies local factorization, analyticOrderNatAt_mul, and preservation of order under composition with nonzero derivative; IsolatedZeros.lean supplies the identity principle and nonvanishing-product infrastructure. OfScalars.lean supports convergent scalar power series. Log.lean:160 supplies exp_two_pi_mul_I_mul_div_eq_one_iff. The targeted searches found no matching cyclic-product descent or local multiplier-order theorem. No proposed-name collision was found in the local DAG or searched worktrees. All pinned dependency checkouts were clean. The exact proposed types and cited order, identity, and exponential lemmas had only propext, Classical.choice, and Quot.sound in their transitive axiom lists.
