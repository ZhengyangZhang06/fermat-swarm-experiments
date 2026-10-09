<!-- theorem-id: fermat-p10/root.level_one_valence_inequality-a1 -->

## Theorem `Submission.p10_17ae7b7d_level_one_valence_inequality`

Let k be an even natural number and F,A:ℂ→ℂ. Put ℍ={z:Im z>0} and ρ=(−1+i√3)/2. Assume F is holomorphic on ℍ and has a nonzero value there; F(z+1)=F(z) and F(−1/z)=zᵏF(z) for every z∈ℍ; A is analytic at zero; and some real Y satisfies F(z)=A(exp(2πiz)) whenever z∈ℍ and Im z≥Y. Then, with the natural orders cast to ℝ, analyticOrderNatAt A 0 + analyticOrderNatAt F i/2 + analyticOrderNatAt F ρ/3 ≤ k/12.

Node: `root.level_one_valence_inequality-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/10

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/421, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/422, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/423, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/424

## Lean problem

Declaration: `Submission.p10_17ae7b7d_level_one_valence_inequality`

```lean
∀ (k : ℕ) (F A : ℂ → ℂ), Even k → DifferentiableOn ℂ F {z : ℂ | 0 < z.im} → (∃ z : ℂ, 0 < z.im ∧ F z ≠ 0) → (∀ z : ℂ, 0 < z.im → F (z + 1) = F z) → (∀ z : ℂ, 0 < z.im → F (-1 / z) = z ^ k * F z) → AnalyticAt ℂ A 0 → (∃ Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im → F z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) → (analyticOrderNatAt A 0 : ℝ) + (analyticOrderNatAt F Complex.I : ℝ) / 2 + (analyticOrderNatAt F ((-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) : ℝ) / 3 ≤ (k : ℝ) / 12
```

### Frozen project context

`Fermat/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean` at `a97febc53b1c4d489edc54ca44132af7a21279b3` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.CuspSpace.cuspDenomAux_infty
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one

set_option autoImplicit false

theorem CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero (N : ℕ) [NeZero N]
    (hg : ModularCurve.genusFormula N = 0) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f = 0 := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.level_one_valence_inequality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Establish finite analytic orders and the identity principle. A holomorphic function on an open subset of ℂ has a local Taylor series by DifferentiableOn.analyticAt in the pinned Mathlib/Analysis/Complex/CauchyIntegral.lean:625. A first nonzero coefficient in degree m gives h(z)=(z−v)ᵐb(z), where b is holomorphic and b(v)≠0. Its exponent is unique: cancellation by the smaller of two proposed powers, followed by a limit at v, excludes unequal exponents with nonzero leading factors. On a smaller disk b is nowhere zero, so h has at most one zero there. On a connected open set, the set E of points near which h vanishes identically is relatively open. At a point outside E the Taylor series cannot be zero, and its factorization gives a neighborhood disjoint from E. Thus the complement is relatively open as well. A nonzero value forces E to be empty. Consequently all orders are finite, zeros are isolated, and a compact subset contains only finitely many zeros by a finite cover of such neighborhoods. Applied to a difference, this also proves the identity principle. The factorization exponent agrees with analyticOrderNatAt by AnalyticAt.analyticOrderNatAt_eq_iff in Mathlib/Analysis/Analytic/Order.lean:101.

2. The half-plane is convex, hence connected, so step 1 applies to F. The analytic germ of A at zero cannot be zero: otherwise F(z)=A(exp(2πiz)) would vanish on a nonempty open upper half-plane, because |exp(2πiz)|=exp(−2π Im z) tends to zero. The identity principle would contradict F's nonzero value. Let m∞ be the finite order of A and write A(q)=q^{m∞}B(q) near zero with B holomorphic and B(0)≠0. Shrinking the neighborhood makes B nowhere zero. The exponential is nonzero, so F has no zeros above some height. Away from its zeros put L=F′/F. At a zero v of order m, local factorization gives L(z)=m/(z−v)+b′(z)/b(z), where the second term is holomorphic near v.

3. Choose Y>1 above the expansion threshold and above the zero-free height, and define D_Y={z: |Re z|≤1/2, |z|≥1, 0<Im z≤Y}. These inequalities imply Im z≥√3/2, so D_Y is closed, bounded, compact, and contained in ℍ. Its interior O_Y is given by −1/2<x<1/2 and √(1−x²)<y<Y. Its boundary is the lower unit-circle arc from ρ through i to ρ+1, two vertical sides, and a horizontal top. It contains finitely many zeros of F. Increasing Y beyond the zero-free height introduces no additional zeros.

4. We prove the argument principle needed for this region. Let V be connected and open, h holomorphic with a nonzero value on V, and Ω nonempty, bounded, and open with compact closure K⊆V. Suppose the boundary is a finite disjoint union of piecewise regular simple closed curves made of finitely many segments and circular arcs. Suppose every boundary point has an orientation-preserving rigid coordinate chart in which the boundary is a Lipschitz, piecewise continuously differentiable graph and Ω lies locally above the graph. If h has no boundary zeros, then ∫∂Ω h′/h dz=2πi∑_{v∈Ω,h(v)=0}ordᵥh, with Ω on the left of its oriented boundary. Steps 5–7 prove this assertion without appealing to the desired valence inequality.

5. By step 1 there are finitely many zeros in K, all interior. The identity principle supplies a nonzero point of h in Ω. Choose disjoint small closed disks about the zeros, contained in Ω, containing no other zero, and avoiding that nonzero point. Remove them to obtain a nonempty open Ω′ with compact zero-free closure K′. The added circular boundary components satisfy the same local graph condition. The function h′/h is holomorphic on a neighborhood of K′ and has a local primitive at every point. To see the latter directly, integrate its local power series coefficientwise. On smaller disks termwise differentiation follows from bounds by nᵈ(r/R)ⁿ; these bounds also prove convergence of the integrated series. The pinned interface DifferentiableOn.isExactOn_ball in Mathlib/Analysis/Complex/HasPrimitives.lean:290 states this local primitive property. Cover K′ by finitely many disks B(pⱼ,rⱼ) such that each doubled disk B(pⱼ,2rⱼ) lies in a primitive domain.

6. Choose a square grid whose square diameter is smaller than every rⱼ. Each closed square meeting K′ is contained in a single doubled disk: choose x in the intersection and a covering disk containing x, then use the diameter bound. Translate the grid to avoid boundary corners, circle tangencies, grid lines coinciding with boundary segments, and grid vertices on the boundary. Such a translation exists. In a bounded translation window only finitely many grid indices can meet the bounded boundary, and the forbidden translations lie in finitely many straight or circular pieces. A line through the window coinciding with none of the straight pieces meets that union in finitely many points, leaving an allowed translation. Subdivide the grid and genuine boundary at their finitely many intersections. In each square orient the portions bounding Ω′ inside that square with the occupied region on their left. They form a finite balanced directed graph: transverse boundary crossings pair entrances and exits, the one-sided graph charts pair incident edges at genuine corners, and occupancy is locally constant at grid vertices. A finite balanced directed graph decomposes into closed walks by following unused edges to a repeated vertex, deleting the resulting cycle, and repeating. A circular boundary component wholly within a square is already a closed walk. Every such walk lies in a primitive domain, so its integral is zero. Indeed the chain rule and intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le, in the pinned FundThmCalculus.lean:1140, give the primitive's endpoint difference on each parametrized piece; the endpoint differences telescope around the walk.

7. Sum these zero integrals over the finitely many relevant squares. Artificial grid edges cancel in opposite orientations, while every genuine boundary portion occurs exactly once. Thus ∫∂Ω′ h′/h dz=0. Around an excised zero v of order m, write h′/h=m/(z−v)+b′/b. Shrink its disk so that b′/b has a primitive there. Parametrization z=v+re^{it} gives counterclockwise integral 2πim for the first term and zero for the second. The circle is clockwise in ∂Ω′. Restoring all disks yields 0=∫∂Ω h′/h dz−2πi∑ordᵥh, proving step 4.

8. To apply that principle despite boundary zeros of F, make compatible cuts. For each such zero v=x+iy of D_Y remove the closed set |(z−v)/(z−conj(v))|≤ε, using the same sufficiently small ε∈(0,1). Completing squares shows this is the Euclidean disk centered at x+iy(1+ε²)/(1−ε²), with radius 2yε/(1−ε²). It contains v strictly, lies in ℍ because its lowest height is y(1−ε)/(1+ε)>0, and shrinks to v as ε→0. By finiteness and isolation, choose ε so these disks are disjoint, contain no other zero, avoid the top, and meet only the original boundary pieces incident to their designated zero. They can also avoid the interior point i(Y+1)/2 and avoid i unless centered there.

9. These cuts meet the incident boundary half-arcs once and transversely. Parametrize such a half-arc outward from v as z(t)=v+at+O(t²), t≥0, a≠0. In the coordinate w=(z−v)/(z−conj(v)) it becomes w(t)=λt+O(t²), λ≠0. Segment and circle parametrizations are real analytic, so d|w(t)|²/dt=2|λ|²t+O(t²)>0 for small positive t. Hence each sufficiently small circle |w|=ε crosses each incident half-arc exactly once and transversely. The compact remainder of the original boundary stays away from v. Therefore the cut circle has exactly two intersections with the original boundary.

10. Put Ω_{Y,ε}=O_Y minus the union of the closed cut disks. It is open, bounded, and nonempty, and its closure is compact in ℍ. On each cut circle, membership in O_Y changes at each transverse crossing and is constant between crossings; precisely one of the two arcs lies inside O_Y. That arc replaces the short original boundary interval through v. The replacement neighborhoods are disjoint and meet no unrelated boundary pieces, so the replacements form a simple closed piecewise regular boundary made of segments and circular arcs. This is the whole boundary: a boundary point of the retained region must lie either on a retained original piece or on a cut circle in the original closure.

11. Verify the local graph hypothesis of step 4. Smooth boundary pieces have bounded-slope graph representations after rotation. The original lower corners have interior angle π/3, and top corners have angle π/2. At a new transverse join, the original interior-side condition and the exterior-of-disk condition give inward tangent half-planes whose intersection is a wedge with angle strictly between zero and π. Rotate its inward bisector upward. Both incident curves then have bounded-slope graph representations, and the region is locally above their maximum. This maximum is Lipschitz and piecewise continuously differentiable. The same construction works at original corners. Thus every boundary point satisfies the required one-sided graph condition.

12. The cuts match exactly under modular identifications. For a real determinant-one Möbius map M(z)=(az+b)/(cz+d), subtraction of fractions gives (M(z)−M(v))/(M(z)−conj(M(v)))=((z−v)/(z−conj(v)))·((c·conj(v)+d)/(cv+d)). The last factor has modulus one, since its numerator and denominator are nonzero conjugates. Applying the identity also to M⁻¹ shows that M maps the entire ε-disk at v to the ε-disk at M(v). The transformation equations preserve zeros. Thus S(z)=−1/z pairs the lower-arc cuts and preserves the cut at i, while T(z)=z+1 pairs the vertical-side cuts; both match the disks at ρ and ρ+1. Locality prevents unrelated cuts from interfering. Paired zeros have equal orders: translation has derivative 1; S has nonzero derivative throughout ℍ; and its multiplier zᵏ never vanishes there. Substitution into local factorizations therefore preserves the exponent. The only S-fixed point on the lower arc is i, since z²=−1 has only i in ℍ.

13. Orient the boundary positively: lower arc clockwise from ρ to ρ+1, right side upward, top right-to-left, and left side downward. Differentiated periodicity gives L(z+1)=L(z), so the exactly matching retained vertical portions cancel. In the zero-free upper region, the q-expansion yields L(z)=2πi(m∞+qB′(q)/B(q)), q=exp(2πiz). The quotient B′/B is bounded on a sufficiently small closed disk. Since |q|=exp(−2πY) on the top, the error tends uniformly to zero as Y→∞. The top has length one and displacement −1, so its integral tends to −2πim∞. The estimate used here follows by parametrizing each piece and applying the integral norm inequality: the integral's norm is at most the supremum of the integrand's norm times the path length.

14. Differentiating F(−1/z)=zᵏF(z) and dividing away from zeros gives L(−1/z)/z²=k/z+L(z). Let E be the left half of the lower unit arc, oriented from ρ to i. S maps E to the right half with orientation opposite to the boundary orientation. On the exactly paired retained portions, change of variables cancels the L terms and leaves −k∫ dz/z over the retained part of E. On the complete E the argument decreases from 2π/3 to π/2, so ∫E dz/z=−iπ/6. The omitted arc lengths tend to zero, and k/z is bounded on the unit circle. Therefore the retained lower-arc contribution tends to kiπ/6=2πi·k/12. This cancellation occurs before taking limits and does not assume separate convergence at a boundary zero.

15. Consider an indentation at a boundary zero v of order m. Solving w=(z−v)/(z−conj(v)) gives z−v=(v−conj(v))w/(1−w), hence dz/(z−v)=dw/w+dw/(1−w). The indentation runs clockwise on |w|=ε because the retained region lies outside the removed disk. This holomorphic coordinate has nonzero derivative at v and preserves oriented angles. If θ is the original interior angle, the endpoint directions approach its tangent rays, and directions strictly inside the tangent sector lie in O_Y at sufficiently small radius. Thus the indentation's angular change tends to −θ, and ∫dw/w tends to −iθ. The other integral has magnitude at most 2πε/(1−ε), tending to zero. The inverse coordinate has bounded derivative near zero, so indentation length also tends to zero. The holomorphic remainder b′/b in L is bounded nearby and contributes a quantity tending to zero. The total indentation contribution consequently tends to −imθ.

16. At i the original boundary is smooth, so θ=π and the contribution is −πi·ordᵢF. At ρ the inward tangent rays have arguments π/6 and π/2, giving θ=π/3. The corner ρ+1 has the same angle and, by translation, the same order. Together the corners contribute −(2πi/3)·ordρF. Every other boundary zero is smooth and belongs to a distinct equal-order S-pair on the lower arc or T-pair on the vertical sides. Each pair contributes −2πi times its common order. There are no top zeros. A nonzero value at i or at a lower corner has order zero, so the same formula applies there without a cut.

17. Apply the argument principle of steps 4–7 with V=ℍ, h=F, and Ω=Ω_{Y,ε}. Steps 8–11 verify its geometric and compactness hypotheses. Its boundary is zero-free: every original boundary zero has been removed, and each indentation circle lies in a disk whose only zero is its designated point, strictly inside. No zero originally in O_Y is removed, because every cut disk contains no other zero. Therefore the right side of the principle is the sum of the original interior zero orders. First let ε→0. The vertical integrals cancel exactly; steps 14–16 give the limits of the lower arc and indentations. Then let Y→∞. All zero counts have stabilized above the zero-free height, and the top has the limit from step 13. Dividing by 2πi and rearranging gives m∞+ordᵢF/2+ordρF/3+R_interior+R_boundary=k/12, where R_interior sums the interior zero orders and R_boundary contains one common order from each nonelliptic boundary pair.

18. Every summand in these two remainders is a nonnegative integer. Discard them to obtain m∞+ordᵢF/2+ordρF/3≤k/12 in ℝ. Steps 1–2 established analyticity and finite order before using any natural order, and identify these three orders with analyticOrderNatAt A 0, analyticOrderNatAt F Complex.I, and analyticOrderNatAt F ((−1+(Real.sqrt 3)·Complex.I)/2), respectively. This is exactly the stated Lean inequality.

## Key steps

1. Establish finite orders, isolated zeros, compact zero finiteness, and the identity principle.
2. Show the cusp germ is nonzero and obtain a zero-free upper region.
3. Construct the truncated fundamental region.
4. Prove the required argument principle using local primitives and a finite grid.
5. Construct compatible cuts around boundary zeros and verify their boundary geometry.
6. Match cuts and orders under S and T.
7. Compute the vertical cancellation, top limit, and paired lower-arc integral.
8. Compute indentation limits and the elliptic angle contributions.
9. Apply the argument principle, take the limits, and discard the nonnegative remaining orders.

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


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
