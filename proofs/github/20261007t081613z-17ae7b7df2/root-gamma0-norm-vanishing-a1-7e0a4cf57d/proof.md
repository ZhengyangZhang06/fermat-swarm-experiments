# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.gamma0_norm_vanishing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write G=SL₂(ℤ), H=Γ₀(N), S=((0,−1),(1,0)), T=((1,1),(0,1)), and U=ST. Apply the sibling gamma0_coset_counts and transfer by inversion to right cosets. The set H\G is finite with μ elements, c right-T cycles, e₂ right-S fixed cosets, and e₃ right-U fixed cosets. Inversion changes each permutation to its inverse, which preserves fixed-point and orbit counts. Since f≠0, CuspForm.ext and the pointwise description of zero give a nonzero value of f on ℍ. Its holo′ field and UpperHalfPlane.mdifferentiable_iff in the pinned Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean:79 give ordinary complex holomorphy. ArithmeticSubgroups.lean:95–98 identifies the subgroup coercion with the image of H in GL₂(ℝ).

2. For α=((a,b),(r,s))∈G define hα(z)=(rz+s)⁻²f((az+b)/(rz+s)) on ℍ. The denominator cannot vanish: if r≠0 its only possible zero is real, and if r=0 the determinant equation forces s≠0. Direct subtraction of conjugates gives Im(αz)=Im z/|rz+s|², and differentiation gives α′(z)=(rz+s)⁻². The inverse matrix supplies the inverse transformation. Thus α acts biholomorphically on ℍ, and hα is holomorphic with a nonzero value. This is the weight-two slash formula of ModularForm.SL_slash_apply in the pinned SlashActions.lean:162.

3. Put j(α,z)=rz+s. Matrix multiplication gives j(αβ,z)=j(α,βz)j(β,z), hence slash associativity. Since f is slash-invariant under H, hηα=hα for η∈H. Therefore hα depends only on the right coset Hα. All these functions may be extended by zero outside ℍ without changing their local properties inside ℍ.

4. Every hα has uniform decay at imaginary infinity. Let w≥1 be the length of the right-T cycle of Hα. Its closing relation gives αTʷα⁻¹∈H. The real image of Tʷ=((1,w),(0,1)) is nonscalar, fixes infinity, has determinant 1 and trace 2, and thus has discriminant zero. Conjugation preserves determinant, trace, and nonscalarity, so the real image of αTʷα⁻¹ is parabolic and fixes α∞. This is a witness for IsCusp at α∞, under Mathlib/NumberTheory/ModularForms/Cusps.lean:58. The field zero_at_cusps′ and OnePoint.IsZeroAt in BoundedAtCusp.lean:54 therefore imply that f slashed by α tends to zero at imaginary infinity. UpperHalfPlane.isZeroAtImInfty_iff in FunctionsBoundedAtInfty.lean:70 gives precisely: for every ε>0 there is Y such that |hα(z)|≤ε for all z∈ℍ with Im z≥Y.

5. Establish the local analytic facts needed for the product. Holomorphy on an open set gives Taylor series by DifferentiableOn.analyticAt. At a point where the germ is nonzero, its first nonzero coefficient gives h(z)=(z−v)ᵐb(z) with b holomorphic and b(v)≠0. The exponent is unique by cancellation away from v and passage to the limit. For a holomorphic function on a connected open set, the set E where it vanishes locally is relatively open; at a point outside E this Taylor factorization gives a neighborhood with at most one zero and hence disjoint from E. Thus the complement is relatively open, and a nonzero value forces E to be empty. Consequently every local order is finite and zeros are isolated. A finite cover by neighborhoods containing at most one zero proves finiteness of zeros on compact subsets. A finite family of such functions has a nonzero product somewhere: choose a closed disk of positive radius inside the domain; their finite combined zero set cannot cover that infinite disk. Multiplying local factorizations adds orders. Composing with a holomorphic map with nonzero derivative preserves order, since ψ(z)−ψ(v)=(z−v)d(z) with d(v)=ψ′(v)≠0. These finite exponents equal analyticOrderNatAt by AnalyticAt.analyticOrderNatAt_eq_iff in Mathlib/Analysis/Analytic/Order.lean:101.

6. Choose representatives of H\G and put F(z)=∏hα(z) on ℍ, extending it by zero outside. The half-plane is convex and therefore connected, so step 5 proves that F is holomorphic and has a nonzero value. The cocycle identity gives hα(βz)=j(β,z)²hαβ(z). Multiplying over the μ cosets and using the permutation induced by right multiplication by β yields F(βz)=j(β,z)^{2μ}F(z). Taking β=T gives F(z+1)=F(z), and taking β=S gives F(−1/z)=z^{2μ}F(z).

7. Apply step 4 with ε=1 to each of the finitely many factors. Above the maximum of their heights, |F(z)|≤1. The sibling periodic_disk_extension with period 1 applies to F and supplies A holomorphic on the unit disk, with finite order at zero, and F(z)=A(exp(2πiz)) throughout ℍ. In particular A is analytic at zero and satisfies the requested expansion above a real height.

8. Fix a right-T cycle of length w≥1, represented by α,αT,…,αT^{w−1}, and put g=hα. The closing coset relation and slash associativity give g(z+w)=g(z), while hαTʲ(z)=g(z+j). The function g is holomorphic, has a nonzero value, and satisfies step 4's decay, which also supplies boundedness. Apply periodic_disk_extension with real period w. It gives g(z)=Aw(exp(2πiz/w)), where Aw is holomorphic on the unit disk and has finite order m≥1 at zero.

9. Set ζ=exp(2πi/w) and P(t)=∏_{j=0}^{w−1}Aw(ζʲt). Since |ζ|=1, all factors are holomorphic on the unit disk. Each has order m, so P has order wm. Its evaluation at exp(2πiz/w) is the contribution of this cycle to F. Cyclic permutation gives P(ζt)=P(t). Write P(t)=∑aₙtⁿ near zero. Differentiated series converge on smaller disks by the bound nᵈ(r/R)ⁿ, so repeated differentiation recovers the coefficients uniquely. Hence aₙ(ζⁿ−1)=0. By Complex.exp_two_pi_mul_I_mul_div_eq_one_iff in the pinned Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:160, ζⁿ=1 exactly when w∣n.

10. Thus only coefficients with indices divisible by w occur. Define C(u)=∑_{ℓ≥0}a_{wℓ}u^ℓ. Choose r>0 strictly inside the convergence radius of P. The convergent series ∑|aₙ|rⁿ bounds the absolute series for C whenever |u|<rʷ. Therefore C is analytic near zero and P(t)=C(tʷ) near zero. Since P's first nonzero coefficient has index wm, C's first nonzero coefficient has index m≥1. The identity exp(2πiz/w)ʷ=exp(2πiz) shows that this cycle contributes a local q-expansion of positive order.

11. Multiply these functions C over all c cycles. Their product B is analytic near zero and has finite order at least c. Above a common height, B(exp(2πiz))=F(z)=A(exp(2πiz)). Every sufficiently small nonzero q has a preimage above that height, since all its preimages have imaginary part −log|q|/(2π). Thus B and A agree on a punctured neighborhood of zero. Continuity gives agreement at zero too, so their germs and orders coincide. Hence analyticOrderNatAt A 0≥c.

12. A right-S fixed coset supplies a factor g=hα satisfying g(−1/z)=z²g(z). Let its finite leading term at i be a(z−i)ᵐ with a≠0. The map −1/z fixes i and has derivative −1 there, whereas z² has value −1. Comparing leading coefficients gives a(−1)ᵐ=−a. Therefore m is odd and m≥1. Every other factor has a nonnegative order. Additivity of orders and the e₂ fixed-coset count give analyticOrderNatAt F i≥e₂.

13. A right-U fixed coset supplies g satisfying g(−1/(z+1))=(z+1)²g(z). The point ρ=(−1+i√3)/2 lies in ℍ and satisfies ρ²+ρ+1=0, ρ³=1, and ρ≠1. Also (ρ+1)²=ρ. The transformation fixes ρ, has derivative ρ² there, and its multiplier has value ρ. For a factor of finite order m with nonzero leading coefficient, coefficient comparison gives ρ^{2m}=ρ. The multiplicative order of ρ is three: it is not one, and ρ²=1 together with ρ³=1 would force ρ=1. Thus 2m≡1 modulo three, so m≡2 modulo three and m≥2. Adding orders over the product and using the e₃ fixed-coset count gives analyticOrderNatAt F ρ≥2e₃. Together with steps 6–11, this proves all the required properties without any genus-zero hypothesis.

## Key steps

1. Obtain the finite right-coset counts from gamma0_coset_counts.
2. Interpret the cusp form and construct holomorphic, nonzero slash factors.
3. Use finite translation cycles to exhibit parabolic cusp stabilizers and obtain decay.
4. Establish finite local orders, product nonvanishing, and order additivity.
5. Form the coset product and prove its weight-2μ transformation equations.
6. Apply periodic_disk_extension to the product and to each translation cycle.
7. Descend each cycle product through t↦tʷ and sum its positive cusp order.
8. Use fixed-point leading-coefficient comparisons at i and ρ.
9. Combine the cusp and elliptic order bounds.

## Reference use

### local-project

Queries:
- `rg -n 'def (genusFormula|nuTwo|nuThree|cuspCount|dedekindPsi)|valence|gamma0_coset_counts|periodic_disk_extension|gamma0_norm_vanishing|level_one_valence_inequality' <snapshot>/project/Definitions <snapshot>/mathlib/Mathlib/NumberTheory/ModularForms`
- `analyticOrderAt_eq_natCast|analyticOrderNatAt_eq_iff|theorem DifferentiableOn.analyticAt|isExactOn_ball|exp_two_pi_mul_I_mul_div_eq_one_iff|exp_eq_exp_iff_exists_int|isZeroAtImInfty_iff|mdifferentiable_iff|SL_slash_def|SL_slash_apply|def IsZeroAt|def IsCusp|def IsParabolic|integral_eq_sub_of_hasDerivAt_of_le`
- `gamma0_coset_counts|periodic_disk_extension|gamma0_norm_vanishing|level_one_valence_inequality|theorem.*[Vv]alence|lemma.*[Vv]alence`
- `rg -n --hidden --no-ignore -g dag.json 'p10_17ae7b7d_(gamma0_coset_counts|periodic_disk_extension|gamma0_norm_vanishing|level_one_valence_inequality)' /mnt/data/zhengyang-workspace/fermat-swarm-projects`
- `git rev-parse HEAD; git status --porcelain --untracked-files=no`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o TargetAbsence.olean TargetAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false -o ChildTypes.olean ChildTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Algebra/Group/Subgroup/Actions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.agents/skills/frozen-header-policy-evidence/evidence.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/diagnostics/operator-approved-header-policy-20261008/controller-compatibility-report.json`
- `/tmp/p10-split-interface-5bnnjwsk/report.json`
- `/tmp/p10-split-interface-5bnnjwsk/TargetAbsence.lean`
- `/tmp/p10-split-interface-5bnnjwsk/ChildTypes.lean`
- `/tmp/p10-split-interface-5bnnjwsk/ChildTypes.log`

The snapshot pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; fresh Git checks matched both revisions and found clean tracked snapshot trees and all nine dependency checkouts matching their pins. The numerical definitions, quotient actions, real-image subgroup coercion, cusp condition, and analytic-order interfaces match the proposed statements. Searches found no existing versions of the four helpers or a named valence theorem in the searched Definitions and modular-form sources, and no conflicting helper-name reservation in the local DAGs. All four literal types compiled after import Submission in a fresh disposable context. Reflexivity probes verified left multiplication on cosets, restriction to the subgroup generated by T, the real-image coercion, and matrix multiplication for S*T. The four type definitions and the selected imported declarations reported only propext, Classical.choice, and Quot.sound. Policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 was checked against its matching entry. Only original lines 10–12 were omitted in the disposable compiler copy; Lean confirmed all 56 targets absent. Original hash 96e3f06b92cb64921c5c4745f0115bb7ca89de8412a80d1d3a1599b7693a0d8a and derived hash fb90bb88b6fa024189bde0f814c11f19649668a957e83b1a7c298dea579e3539 were recorded with exact omitted lines and reversible reconstruction. Original contract and Submission remained byte-identical. These are interface diagnostics, not child-proof or comparator acceptance.
