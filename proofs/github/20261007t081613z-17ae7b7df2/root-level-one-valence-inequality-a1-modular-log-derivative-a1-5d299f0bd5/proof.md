# Parent-supplied natural-language proof

- Parent DAG node: `root.level_one_valence_inequality-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.modular_log_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write T(u)=u+1 and S(u)=−1/u. Both are holomorphic bijections of H: T has inverse u↦u−1, S is its own inverse, and Im S(u)=Im u/|u|²>0. Every u∈H is nonzero. Their derivatives are T′(u)=1 and S′(u)=1/u², both nonzero. F is analytic at every point of H by local analyticity of holomorphic functions.
2. For either φ=T or φ=S, the hypotheses have the form F(φ(u))=J(u)F(u), where respectively J(u)=1 or J(u)=u^k. In both cases J is analytic and nonvanishing on H. At any z∈H, F has a zero germ at z if and only if it has a zero germ at φ(z). Indeed, a zero germ at φ(z) pulls back to a zero germ of F∘φ at z, and division by the nonvanishing J gives a zero germ of F at z. Conversely, a zero germ at z gives a zero germ of F∘φ there; applying the continuous local inverse of φ gives a zero germ at φ(z).
3. If these germs are zero, both analytic orders are infinite and both natural-valued orders are zero, proving the desired equality in this case. Otherwise both orders are finite. Put m=analyticOrderNatAt F z and n=analyticOrderNatAt F (φ(z)). Finite-order factorization gives F(u)=(u−z)^m b(u) near z and F(w)=(w−φ(z))^n c(w) near φ(z), with b and c analytic and their values at the respective centers nonzero.
4. Near z write φ(u)−φ(z)=(u−z)a(u). For T take a(u)=1; for S take a(u)=1/(uz). In either case a is analytic near z and a(z)≠0. Substituting the two factorizations into F(φ(u))=J(u)F(u) gives two factorizations of the same germ, with exponents n and m and nonzero analytic leading factors a(u)^n c(φ(u)) and J(u)b(u). Uniqueness of the factorization exponent gives n=m. Explicitly, if the exponents differed, cancellation of the smaller power on a punctured disk and passage to the center would force one of these leading factors to vanish. This proves both order equalities.
5. Now assume F(z)≠0. The transformation identities and z^k≠0 imply F(T(z))≠0 and F(S(z))≠0. Differentiate the translation identity on the open set H to obtain F′(z+1)=F′(z). Division by the equal nonzero function values yields L(z+1)=L(z).
6. Differentiate the inversion identity. At nonzero z the derivative of u↦u^k is (k:ℂ)z^k/z; this follows from the power rule for k>0 and is also true for k=0. Thus F′(S(z))/z²=z^k F′(z)+(k:ℂ)z^k F(z)/z. Divide by z^k F(z)=F(S(z)), which is nonzero. The result is L(S(z))/z²=(k:ℂ)/z+L(z), proving the remaining conclusion.

## Key steps

1. Verify that T and S are holomorphic bijections of H with nonzero derivatives.
2. Use the nonvanishing multipliers to transport zero germs in both directions.
3. Compare local factorizations to preserve finite orders; handle infinite orders through the definition of analyticOrderNatAt.
4. Differentiate periodicity and divide at nonzero values.
5. Differentiate the inversion law and divide by z^k F(z).

## Reference use

### local-project

Queries:
- `\bvalence\b|argument.?principle|windingnumber`
- `analyticOrderNatAt_eq_iff|analyticOrderAt_ne_top|analyticOrderAt_eq_top`
- `eqOn_zero|eqOn_of|finite|eq_zero_or|frequently`
- `logDeriv_mul|logDeriv_comp|logDeriv_pow`
- `integral_eq_sub_of_hasDerivAt_of_le|norm_integral_le_of_norm_le_const`
- `sed -n '1,150p' project/Definitions/Def_ModularCurve_GenusNumerics.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Calculus/LogDeriv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Searches of mathlib/Mathlib/Analysis/Complex and project/Definitions found no valence, argument-principle, or winding-number implementation. The inspected library supplies local analyticity, the identity principle, finite-order factorization, logarithmic-derivative rules, local primitives, and interval-integral estimates. The cited library declarations passed transitive axiom probes using only propext, Classical.choice, and Quot.sound. All nine installed dependencies matched their pinned revisions and were Git-clean.
