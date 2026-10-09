# Parent-supplied natural-language proof

- Parent DAG node: `root.level_one_valence_inequality-a1`
- Child DAG node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write v=x+iy with y>0 and z=u+it. Since 0<ε<1, the real number 1−ε² is positive. If t>0, then z−conj(v) has imaginary part t+y>0 and is nonzero. Hence the defining norm inequality can be multiplied by its denominator and squared without changing its truth value.
2. The resulting inequality is (u−x)²+(t−y)²≤ε²((u−x)²+(t+y)²). Expanding, dividing by 1−ε², and completing the square gives exactly (u−x)²+(t−y(1+ε²)/(1−ε²))²≤(2yε/(1−ε²))². The radius on the right is positive, so this is precisely membership in the asserted Euclidean closed disk.
3. The center's imaginary part minus the radius equals y(1+ε²−2ε)/(1−ε²)=y(1−ε)/(1+ε)>0. Every point of the Euclidean disk therefore lies in H. Consequently the equivalence in step 2 proves equality of the full sets, including the half-plane condition in D.
4. Fix real a,b,c,d with ad−bc=1. For z∈H, cz+d is nonzero: if c≠0 its imaginary part is c Im z≠0, and if c=0 the determinant equation implies d≠0. Direct multiplication by the conjugate denominator gives Im M(z)=Im z/|cz+d|²>0. The map N(w)=(dw−b)/(−cw+a) has the same properties and satisfies N(M(z))=z and M(N(w))=w on H, by the determinant equation.
5. For z,v∈H, subtraction of fractions gives M(z)−M(v)=(z−v)/((cz+d)(cv+d)). Real coefficients also give conj(M(v))=M(conj(v)), and subtraction with conj(v) gives M(z)−conj(M(v))=(z−conj(v))/((cz+d)(c conj(v)+d)). All denominators are nonzero: those at conjugate points are conjugates of the corresponding nonzero denominators, and M(z)−conj(M(v)) has positive imaginary part. Dividing the two identities yields (M(z)−M(v))/(M(z)−conj(M(v)))=((z−v)/(z−conj(v)))·((c conj(v)+d)/(cv+d)). The final factor has norm one because its numerator is the conjugate of its nonzero denominator. Thus the two pseudohyperbolic ratios have equal norms.
6. Steps 4–5 show that z∈D(v,ε) implies M(z)∈D(M(v),ε), proving one image inclusion. Conversely, if w∈D(M(v),ε), apply the same norm identity to N and the center M(v). It gives N(w)∈D(v,ε), while M(N(w))=w. This proves the reverse inclusion and completes the theorem.

## Key steps

1. Square the defining inequality using its nonzero denominator in H.
2. Complete the square to identify the Euclidean center and radius.
3. Show the entire Euclidean disk lies strictly inside H.
4. Verify that determinant-one real Möbius maps and their inverses preserve H.
5. Compute the transformed ratio and its unit-modulus factor.
6. Apply the inverse transformation to obtain equality of images.

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
