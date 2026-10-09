# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.orbit_product_order-a1`
- Child DAG node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.orbit_product_order-a1.nonzero_dilation_product_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix w, ζ, and A satisfying the hypotheses, define P as stated, and put m = analyticOrderNatAt A 0. Apply AnalyticAt.analyticOrderNatAt_eq_iff to the analyticity and finite-order hypotheses, using the equality analyticOrderNatAt A 0 = m. It supplies b : ℂ → ℂ analytic at zero with b(0) ≠ 0 and A(u) = u^m b(u) throughout a neighborhood U of zero. Here subtraction of zero and scalar multiplication of complex numbers simplify to the displayed formula.
2. For each j < w, the map L_j(t) = ζ^j t is analytic, continuous, and satisfies L_j(0) = 0. Hence A ∘ L_j and b ∘ L_j are analytic at zero. The inverse image of U under L_j is a neighborhood of zero. Their finite intersection V is a neighborhood on which A(ζ^j t) = (ζ^j t)^m b(ζ^j t) holds simultaneously for every j < w. If w = 0, take V = ℂ. The finite product of the analytic functions A ∘ L_j is analytic at zero, proving analyticity of P.
3. Define D(t) = ∏_{j=0}^{w−1} (ζ^(j*m) b(ζ^j t)). Every factor is analytic at zero, so D is analytic there. At zero, each factor equals ζ^(j*m) b(0), which is nonzero because ζ ≠ 0 and b(0) ≠ 0. A finite product of nonzero complex numbers is nonzero, so D(0) ≠ 0. This also covers w = 0, when D(0) = 1.
4. For t in V and j < w, the power identities and commutativity of complex multiplication give A(ζ^j t) = ζ^(j*m) t^m b(ζ^j t) = t^m (ζ^(j*m) b(ζ^j t)). Multiplying these identities gives P(t) = (t^m)^w D(t) = t^(w*m) D(t), using m*w = w*m. The same identity holds for the empty product because t^0 = 1.
5. Apply AnalyticAt.analyticOrderAt_eq_natCast to P, with the analytic nonvanishing factor D from steps 3–4. This gives analyticOrderAt P 0 = (w*m : ℕ∞). A natural-number cast into ℕ∞ is not ⊤, establishing finite order.
6. By definition analyticOrderNatAt is the natural value of analyticOrderAt. Taking that value in the equality from step 5 gives analyticOrderNatAt P 0 = w*m = w · analyticOrderNatAt A 0. Together with steps 2 and 5, this proves all three conclusions.

## Key steps

1. Factor A locally as t^m b(t), where b is analytic and b(0) ≠ 0.
2. Pull the factorization back along finitely many dilations and prove P analytic.
3. Construct an analytic residual product D with D(0) ≠ 0.
4. Multiply the local factorizations to obtain P(t) = t^(w*m) D(t), including the empty-product case.
5. Apply the order characterization and take the natural value to obtain both order conclusions.

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
