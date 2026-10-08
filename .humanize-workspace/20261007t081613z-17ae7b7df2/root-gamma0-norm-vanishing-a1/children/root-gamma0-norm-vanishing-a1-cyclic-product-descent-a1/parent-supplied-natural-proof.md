# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_norm_vanishing-a1`
- Child DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix w and A satisfying the hypotheses, and put ζ=exp(2πi/w). Since w>0, its complex cast is nonzero. The exponential power identity gives ζ^n=exp(2πin/w) for every natural n. Complex.exp_two_pi_mul_I_mul_div_eq_one_iff therefore gives ζ^n=1 exactly when w divides n. In particular ζ^w=1. The exponent defining ζ has real part zero, so ‖ζ‖=1 and ζ≠0.
2. Put m=analyticOrderNatAt A 0. The analyticity and finite-order hypotheses, using AnalyticAt.analyticOrderNatAt_eq_iff, give an analytic function b near zero with b(0)≠0 and A(t)=t^m b(t) on a neighborhood of zero. Define P(t)=∏_{j=0}^{w−1}A(ζ^j t). Each factor is analytic near zero. On a sufficiently small disk the factorization of A applies simultaneously to every ζ^j t, because ‖ζ^j t‖=‖t‖. Consequently P(t)=t^{wm}D(t), where D(t)=∏_{j=0}^{w−1}(ζ^{jm}b(ζ^j t)). The function D is analytic near zero and D(0)≠0, since every factor in D(0) is nonzero. Thus P has finite order wm.
3. Choose R>0 such that P has a convergent Taylor expansion P(t)=∑_{n≥0}a_n t^n for ‖t‖<R. Shrink R if necessary so that the preceding factorization also holds there. Comparing this factorization with the Taylor series shows that a_n=0 for n<wm and a_{wm}=D(0)≠0: multiplication of the Taylor series of D by t^{wm} shifts its coefficients by wm.
4. For every t, the product P(ζt) has factors A(ζ^{j+1}t). The final factor is A(ζ^w t)=A(t), and the other factors are precisely the remaining factors of P(t). Commutativity of complex multiplication therefore gives P(ζt)=P(t).
5. Since ‖ζ‖=1, both Taylor expansions in this equality converge for ‖t‖<R. Uniqueness of coefficients gives a_n ζ^n=a_n for every n. To see the uniqueness directly, a first nonzero coefficient of the difference of two such series would, after division by its power of t, have a nonzero limit at zero; the higher terms tend to zero by absolute convergence on a smaller disk, contradicting that the difference vanishes. Hence a_n(ζ^n−1)=0. By step 1, a_n=0 whenever w does not divide n.
6. Choose 0<r<R. The series ∑_{n≥0}|a_n|r^n converges. For |u|<r^w, the series ∑_{ℓ≥0}a_{wℓ}u^ℓ converges absolutely, since its absolute terms are bounded by the corresponding terms of ∑_{ℓ≥0}|a_{wℓ}|r^{wℓ}, which is a subseries of the preceding convergent nonnegative series. Define C(u) by this power series when |u|<r^w and define C(u)=0 outside that disk. This power series has positive convergence radius, so C is analytic at zero.
7. If ‖t‖<r, then |t^w|<r^w because w>0. Absolute convergence permits reindexing the Taylor series of P by its nonzero coefficients. Step 5 gives P(t)=∑_{ℓ≥0}a_{wℓ}t^{wℓ}=∑_{ℓ≥0}a_{wℓ}(t^w)^ℓ=C(t^w). This also holds at t=0 by evaluation of the convergent series.
8. For ℓ<m, positivity of w gives wℓ<wm, so the coefficient a_{wℓ} of C is zero. Its coefficient at index m is a_{wm}≠0. Factoring its convergent series therefore gives C(u)=u^m E(u) near zero, where E is analytic and E(0)=a_{wm}≠0. The local order characterization now gives analyticOrderAt C 0 ≠ ⊤ and analyticOrderNatAt C 0=m=analyticOrderNatAt A 0. Together with steps 6–7, this proves every asserted property.

## Key steps

1. Establish that ζ is a primitive w-th root of unity of norm one.
2. Factor A at zero and show the cyclic product has finite order w times the order of A.
3. Use cyclic permutation to prove rotation invariance of the product.
4. Use uniqueness of Taylor coefficients to eliminate indices not divisible by w.
5. Construct the descended convergent power series from coefficients a_{wℓ}.
6. Reindex the series to obtain P(t)=C(t^w) near zero.
7. Identify the first nonzero coefficient of C and recover the order of A.

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
