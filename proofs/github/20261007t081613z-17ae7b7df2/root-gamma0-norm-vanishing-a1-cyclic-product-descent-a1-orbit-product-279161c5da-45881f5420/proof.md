# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.orbit_product_order-a1`
- Child DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.orbit_product_order-a1.cyclic_product_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix w, ζ, and A satisfying the hypotheses, and fix t ∈ ℂ. Since w > 0, put n = w−1, so w = n+1. For each natural number j define f(j) = A(ζ^j t). Thus P(t) is the product of f(j) over j in Finset.range (n+1).
2. The identity ζ^j(ζt) = ζ^(j+1)t follows from associativity and the successor power identity. Applying A to it in every factor shows P(ζt) = ∏_{j∈Finset.range (n+1)} f(j+1).
3. The endpoints agree: f(n+1) = A(ζ^w t) = A(t), using ζ^w = 1, while f(0) = A(ζ^0 t) = A(t). Therefore f(n+1) = f(0).
4. Let Q = ∏_{j∈Finset.range n} f(j+1). Splitting off the last factor of the shifted product, by Finset.prod_range_succ, gives P(ζt) = Q f(n+1). Splitting off the first factor of the original product, by Finset.prod_range_succ', gives P(t) = Q f(0). Step 3 makes these expressions equal. When n = 0, Q = 1 and both identities remain valid. Since t was arbitrary, P(ζt) = P(t) for every t ∈ ℂ.

## Key steps

1. Write the positive integer w as n+1.
2. Rewrite evaluation at ζt as the product with exponents shifted by one.
3. Use ζ^w = 1 to identify the last shifted factor with the original first factor.
4. Apply the two endpoint product identities to conclude equality, including w = 1.

## Reference use

### local-project

Queries:
- `analyticOrderNatAt_eq_iff|analyticOrderAt_eq_natCast|analyticOrderAt_prod|analyticOrderNatAt.*prod|prod_range_succ|prod_range_succ_comm`
- `cyclic.*(product|prod|descent)|orbit.*product|rotation.*(product|invariant)|analyticOrderNatAt`
- `finset_prod|Finset.*prod|analyticAt.*mul|lemma AnalyticAt.mul`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Constructions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`

The snapshot revisions match project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Order.lean supplies AnalyticAt.analyticOrderNatAt_eq_iff and AnalyticAt.analyticOrderAt_eq_natCast; Constructions.lean supplies Finset.analyticAt_fun_prod; Basic.lean supplies Finset.prod_range_succ and Finset.prod_range_succ'. The targeted project search found no matching cyclic/orbit-product theorem. All nine build dependencies match their pins and are clean. Both proposed types elaborated after literal import Submission in diagnostics/cpo-typecheck-0t_gyk3m/TypesAfterSubmission.lean. The private compiler copy omitted only policy-listed lines 10–12; the policy digest matched, reconstruction recovered the original bytes, and Lean confirmed all 56 omitted targets absent. The checked types and cited library lemmas use only propext, Classical.choice, and Quot.sound. Complex multiplication uses Complex.commRing.toCommMonoid. These diagnostics establish compatibility, not comparator acceptance of child proofs.
