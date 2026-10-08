# Parent-supplied natural-language proof

- Parent DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1`
- Child DAG node: `root.odd_division_detection-a1.odd_prepsi_torsion-a1.torsion_eds_exists-a1.torsion_kernel_cardinality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k and W satisfying the hypotheses. Let E be the projective Weierstrass cubic, with identity O and affine coordinate functions x and y. The nonzero discriminant makes E smooth. It is geometrically integral: over the algebraically closed field, distinct components of a reducible projective plane cubic would intersect, producing a singular point. Its k-points, consisting of O and the nonsingular affine points, identify with W.toAffine.Point, and the chord-and-tangent law gives the same group operation. We use the standard facts that a nonconstant morphism between smooth projective integral curves is finite and surjective, that the multiplicities in each fiber sum to its degree, and that principal divisors have degree zero. These are the curve facts in Silverman, The Arithmetic of Elliptic Curves, second edition (2009), Chapter II, §§2–3. The Weierstrass group law and local parameters used here are treated in Chapter III, §§2–4, and Chapter IV, §1.
2. At O put t = −x/y and s = −1/y. The equation becomes s = t³ + a₁ts + a₂t²s + a₃s² + a₄ts² + a₆s³. Its derivative with respect to s, after moving the right side to the left, is 1 at (0,0). Consequently t is a uniformizer, and solving successively for the coefficients of s gives s = t³ plus terms of higher degree. Since x = t/s and y = −1/s, the leading terms of x and y are respectively t⁻² and −t⁻³.
3. The regular group law has expansion F(t₁,t₂) = t₁ + t₂ plus terms of total degree at least two: its restrictions F(t₁,0) = t₁ and F(0,t₂) = t₂ force these linear coefficients. Induction on j therefore gives t ∘ [j] = jt plus terms of degree at least two for every positive integer j. Characteristic zero makes the coefficient j nonzero. For any P, the identity [j](P + Q) = [j]P + [j]Q transports this computation by translations to the local rings at P and [j]P. Thus [j] has local multiplicity one everywhere. It is nonconstant, hence finite and surjective. Write d_j for its degree. Every fiber consists of d_j distinct k-points, because k is algebraically closed and every local multiplicity is one. In particular E[j] = {P : [j]P = O} is finite with d_j elements. Write K_j for the divisor consisting of these points, each with coefficient one; then K_j = [j]⁎(O) and deg K_j = d_j.
4. Complete the square by putting z = y + (a₁x + a₃)/2 and G(X) = 4X³ + b₂X² + 2b₄X + b₆. The equation is z² = G(x)/4. The cubic G has three distinct roots in k: a repeated root α would make (α,0) singular in these coordinates, contrary to smoothness. Negation sends (x,z) to (x,−z), so its affine fixed points are precisely these three points. They are exactly the nonzero points of E[2]. Thus d₂ = 4, while d₁ = 1. At a nonzero two-torsion point T with x-coordinate α, the nonvanishing of G′(α) makes z a uniformizer and gives x − α = (4/G′(α))z² plus terms of higher order. At any affine point outside E[2], the derivative with respect to y is 2z ≠ 0, so x minus its value is a uniformizer.
5. Fix integers m > r ≥ 1 and set H = x ∘ [m] − x ∘ [r]. At O its leading term is (m⁻² − r⁻²)t⁻². This coefficient is nonzero, because m and r are distinct positive integers in a characteristic-zero field. Hence H is a nonzero rational function.
6. Consider a source point P for which both [m]P and [r]P are affine. Two affine points have the same x-coordinate exactly when they are equal or opposite; this also follows directly from z² = G(x)/4. Suppose first that [m]P = [r]P = Q and Q is not two-torsion. In the translated parameter u at O, write x(Q + R) = x(Q) + c u(R) plus higher-order terms, where c ≠ 0 by step 4. Using P + R as the source, the leading coefficient in H is c(m − r), so its zero at P is simple. If [m]P = −[r]P = Q and Q is not two-torsion, replace the second argument using x(−Q + [r]R) = x(Q − [r]R). The leading coefficient is c(m + r), again nonzero, so the zero is simple. If both images are the same nonzero two-torsion point T, step 4 and translation give x(T + R) = x(T) + c u(R)² plus higher-order terms with c ≠ 0. The leading coefficient of H is then c(m² − r²), so the zero has order two. If the two images are neither equal nor opposite, H is regular and nonzero at P.
7. If exactly one of [m]P and [r]P is O, precisely one summand of H has a pole of order two, so H has order −2 at P. If both images are O, translate the source by P. The expansions from steps 2–3 give the nonzero leading coefficient m⁻² − r⁻² at order −2, so H again has order −2.
8. These cases give the divisor identity div(H) = K_(m+r) + K_(m−r) − 2K_m − 2K_r. Indeed, equal affine images outside two-torsion contribute only to K_(m−r), opposite affine images outside two-torsion contribute only to K_(m+r), and a common nonzero two-torsion image contributes to both. If exactly one image is O, only one of K_m and K_r contributes. If both images are O, all four divisors contribute, giving coefficient 1 + 1 − 2 − 2 = −2. All other coefficients are zero. Every K_j has coefficient one on its support by step 3, so these are exactly the local orders computed above.
9. Taking degrees and using deg div(H) = 0 yields d_(m+r) + d_(m−r) = 2d_m + 2d_r. Set r = 1. For m ≥ 2 this gives d_(m+1) = 2d_m + 2 − d_(m−1). Together with d₁ = 1 and d₂ = 4, induction gives d_j = j² for every j ≥ 1: if the formula holds at m and m−1, then d_(m+1) = 2m² + 2 − (m−1)² = (m+1)².
10. For the given n > 0, step 3 supplies finiteness of E[n], and step 9 gives its cardinality n². Under the point-group identification in step 1, this is exactly the subtype {P : W.toAffine.Point // n • P = 0}. Finiteness and its Nat.card equality follow.

## Key steps

1. Identify the smooth projective Weierstrass cubic and its k-point group with the stated point type.
2. Use t = −x/y to obtain the leading coordinate terms and the linear term jt of multiplication by j.
3. Translate the local calculation to prove that every positive multiplication map is finite, surjective and everywhere unramified.
4. Count the two-torsion points using the separable cubic obtained by completing the square.
5. Compute every local order of x ∘ [m] − x ∘ [r].
6. Take degrees of its divisor to obtain the recurrence for multiplication-map degrees.
7. Solve the recurrence from d₁ = 1 and d₂ = 4 and identify the finite kernel cardinality.

## Reference use

### local-project

Queries:
- `ψ_|Ψ_|ψ₂|preΨ₄|XYIdeal|ordinaryLineAt|division.*polynomial|DivisionPolynomial`
- `Nat.card.*torsion|card.*torsionBy|sum.*(invol|neg|orderOf)|sum.*eq_zero`
- `namespace Point|deriving|instAddCommGroup|instAddGroup|neg_some|two_nsmul|Nonsingular`
- `twoTorsionPolynomial_discr|twoTorsionPolynomial|b_relation`
- `p03_eds_torsion_kernel_card_68cf3476_d4|p03_eds_torsion_kernel_sum_68cf3476_d4`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p03_eds_geometric_split_mce1cixa/ChildTypes.lean`
- `/tmp/p03_eds_geometric_split_mce1cixa/HeaderAbsence.lean`
- `/tmp/p03_eds_geometric_split_mce1cixa/InstanceAxioms.log`
- `/tmp/p03_eds_geometric_split_mce1cixa/receipt.json`

The snapshot records project 81f093181fd6c58dc887fcae5ec8b896996f1885 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; the compiler's mathlib checkout matched and was clean. DivisionPolynomial/Basic.lean already supplies the canonical initial values and recurrences. Affine/Basic.lean supplies nonsingularity from nonzero discriminant; Affine/Point.lean supplies the intended point group, negation and equality-of-x-coordinate criterion. Weierstrass.lean proves that the two-torsion cubic has discriminant 16Δ. The targeted torsion-cardinality and torsion-sum search found no relevant theorem in the searched elliptic-curve and finite-abelian-group modules. The DAG already reserves recurrence uniqueness in another branch; neither proposed identifier was reserved. Both exact child types elaborated after import Submission using a disposable copy of the parent's frozen proof base. Lean confirmed the canonical point-group instances and definitionally identified natural scalar multiplication with nsmulBinRec. The inspected library declarations have only propext, Classical.choice and Quot.sound as transitive axioms. Policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 matched; only listed lines 10 and 11 were omitted, all 37 targets were checked absent under the frozen imports, and byte-exact restoration and dependency-source checks passed. These are interface diagnostics, not comparator acceptance of either proposed theorem.
