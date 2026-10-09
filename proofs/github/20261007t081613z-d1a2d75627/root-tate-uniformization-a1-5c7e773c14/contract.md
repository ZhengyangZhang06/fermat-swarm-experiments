<!-- theorem-id: fermat-p03/root.tate_uniformization-a1 -->

## Theorem `Submission.p03_tate_uniformization_68cf3476`

Let F be a complete characteristic-zero normed field satisfying |x+y|≤max(|x|,|y|), and suppose there is a real r with 0<r<1 such that every nonzero norm value in F equals r^m for some integer m. Let Ω be an algebraically closed algebraic extension of F, equipped with a characteristic-zero normed-field structure, decidable equality, and an ultrametric norm extending the norm of F. Let q∈F satisfy 0<|q|<1, and write qΩ for its image in Ω. For k∈ℕ define s_k=Σ_{d≥1}d^k q^d/(1−q^d). Define T/F by a₁=1, a₂=a₃=0, a₄=−5s₃ and a₆=−(5s₃+7s₅)/12. Define X(u)=Σ_{n∈ℤ}qΩ^n u/(1−qΩ^n u)²−2s₁ and Y(u)=Σ_{n∈ℤ}(qΩ^n u)²/(1−qΩ^n u)³+s₁, with s₁ mapped to Ω. Every Lambert series and the product ∏_{d≥1}(1−q^d)^24 converge. The invariants satisfy c₄(T)=1+240s₃, c₆(T)=−1+504s₅, and Δ(T)=q∏_{d≥1}(1−q^d)^24≠0. For every u∈Ω× outside qΩ^ℤ, both bilateral series converge. There exists a surjective homomorphism θ from Ω×, regarded additively, to the point group of WeierstrassCurve.Affine.baseChange T.toAffine Ω, whose kernel consists exactly of qΩ^ℤ, which sends each nonkernel u to the nonsingular affine point (X(u),Y(u)), and satisfies θ(σu)=σθ(u) for every F-automorphism σ of Ω.

Node: `root.tate_uniformization-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/3

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/352, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/354, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/355, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/356, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/357

## Lean problem

Declaration: `Submission.p03_tate_uniformization_68cf3476`

```lean
∀ (F Ω : Type) [NormedField F] [CharZero F] [CompleteSpace F] [NormedField Ω] [CharZero Ω] [DecidableEq Ω] [NormedAlgebra F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω], (∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → (∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → (∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = r ^ n) → ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 → let s : ℕ → F := fun k => ∑' d : ℕ, ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1)); let T : WeierstrassCurve F := ⟨1, 0, 0, -5 * s 3, -(5 * s 3 + 7 * s 5) / 12⟩; let qΩ : Ω := algebraMap F Ω q; let X : Ω → Ω := fun u => (∑' n : ℤ, qΩ ^ n * u / (1 - qΩ ^ n * u) ^ 2) - 2 * algebraMap F Ω (s 1); let Y : Ω → Ω := fun u => (∑' n : ℤ, (qΩ ^ n * u) ^ 2 / (1 - qΩ ^ n * u) ^ 3) + algebraMap F Ω (s 1); (∀ k : ℕ, Summable (fun d : ℕ => ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1)))) ∧ Multipliable (fun d : ℕ => (1 - q ^ (d + 1)) ^ 24) ∧ T.c₄ = 1 + 240 * s 3 ∧ T.c₆ = -1 + 504 * s 5 ∧ T.Δ = q * (∏' d : ℕ, (1 - q ^ (d + 1)) ^ 24) ∧ T.Δ ≠ 0 ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → Summable (fun n : ℤ => qΩ ^ n * (u : Ω) / (1 - qΩ ^ n * (u : Ω)) ^ 2) ∧ Summable (fun n : ℤ => (qΩ ^ n * (u : Ω)) ^ 2 / (1 - qΩ ^ n * (u : Ω)) ^ 3)) ∧ ∃ θ : Additive Ωˣ →+ (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Point, Function.Surjective θ ∧ (∀ u : Ωˣ, θ (Additive.ofMul u) = 0 ↔ ∃ m : ℤ, (u : Ω) = qΩ ^ m) ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → ∃ h : (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Nonsingular (X (u : Ω)) (Y (u : Ω)), θ (Additive.ofMul u) = WeierstrassCurve.Affine.Point.some (X (u : Ω)) (Y (u : Ω)) h) ∧ ∀ (σ : Ω ≃ₐ[F] Ω) (u : Ωˣ), θ (Additive.ofMul (Units.map σ.toMonoidHom u)) = σ • θ (Additive.ofMul u)
```

### Frozen project context

`Fermat/Thm_WeierstrassCurve_galoisRep_ordinaryLineAt.lean` at `81f093181fd6c58dc887fcae5ec8b896996f1885` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_galoisRep_ordinaryLineAt.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_GaloisRep_Residual
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.galoisRep_ordinaryLineAt (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel)
    (hord : (p : ℤ) ∣ W.Δ ∨ ∃ i, 1 ≤ i ∧ i < (p ^ 2 - 1) / 2 ∧ ¬ (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ L : Submodule (ZMod p)
        (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p),
      L ≠ ⊤ ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ v : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
            (W.map (Int.castRingHom ℚ)) p σ v - v ∈ L := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.tate_uniformization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Identify F with its image in Ω; NormedAlgebra ensures that this inclusion preserves norms. Every finite intermediate extension E/F is complete, by completeness of finite-dimensional normed spaces over a complete nontrivially normed field. The element q ensures nontriviality. This is the pinned FiniteDimensional.complete theorem. Such E is discretely valued: elements with norms in distinct cosets of |F×| are F-linearly independent, because terms in a nonzero linear combination then have distinct norms and the largest cannot cancel. Thus |E×|/|F×| has order at most [E:F], and raising values to [E:F]! puts them in |F×|⊆r^ℤ. The value group of E is consequently discrete. Its valuation ring is a complete discrete valuation ring: a smallest positive valuation gives a uniformizer, division by its powers reduces every nonzero element to a unit, and choosing least valuations shows that every nonzero ideal is principal. The valuation ring is closed, and norm completeness agrees with completeness for powers of its maximal ideal. We use PowerSeries.exists_isWeierstrassFactorization: over a complete local ring, a formal power series with nonzero reduction is a distinguished monic polynomial times a unit power series, with polynomial degree equal to the order of the reduced series. This preparation theorem is proved in the pinned library and is cited there as Washington, Introduction to Cyclotomic Fields, second edition, Theorem 7.3.

2. Consider a nonzero Laurent series f(u)=Σ_{j∈ℤ}c_j u^j over a finite E/F, converging on a closed annulus a≤|u|≤b with endpoint radii in |Ω×|. Thus |c_j|b^j tends to zero as j→+∞ and |c_j|a^j tends to zero as j→−∞. At radius ρ its Gauss norm is N_f(ρ)=max_j|c_j|ρ^j. Only finitely many indices can maximize on a compact radius interval: both tails tend uniformly to zero, whereas any fixed nonzero term gives a positive lower bound. A unique maximizing term precludes a zero. The maximizing index can change at only finitely many radii, each belonging to |Ω×|, since equality of two term norms expresses a power of that radius as the norm of an algebraic element and Ω contains the required root.

3. At a tie radius ρ choose α∈Ω× with |α|=ρ and enlarge E finitely to contain α. Divide f(αz) by a coefficient of maximal norm. All coefficients are integral and only finitely many have nonzero reduction, giving a nonzero residue Laurent polynomial P(z). If its extreme exponents are m,n, it has n−m nonzero roots with multiplicity over the residue algebraic closure. The residue field of Ω is algebraically closed: lift a monic residue polynomial to integral coefficients in Ω, split it in Ω, and observe that all roots are integral, since a nonintegral root would make its leading term uniquely largest. Reducing the factorization proves the claim. Enlarge E finitely to contain lifts of the finitely many nonzero residue roots of P. These extensions are finite because Ω/F is algebraic.

4. Around a unit lift β of a residue root write z=β+t, |t|<1. Binomial expansion of every positive or negative integer power gives a power series with integral coefficients. Each resulting coefficient converges because the integer binomial coefficients have norm at most one and the original Laurent coefficient tails tend to zero. The reduction has order e, the multiplicity of the chosen residue root. Preparation from step 1 factors this series as a distinguished degree-e polynomial times an integral unit power series. Both converge for |t|<1, and the unit series is nonzero there because its constant term is a unit. All roots of the distinguished polynomial have norm less than one: at norm at least one its monic leading term is uniquely largest. It therefore supplies exactly e zeros with multiplicity in this disk, all algebraic over E. Outside these residue disks the reduction is nonzero. Thus the number of zeros on |u|=ρ is n−m. The dominant exponent is nondecreasing as the radius increases, and its jump at this tie is n−m. Summing over tie radii proves that on an annulus whose boundaries avoid ties the total zero multiplicity is the increase of the maximizing Laurent exponent.

5. The analytic operations below stay within this Laurent-series class. Products converge uniformly on closed annuli wherever their factors do; the infinite tails used below have geometric bounds. Division by a zero factor u−a preserves Laurent analyticity: subtract f(a)=Σc_j a^j and divide each u^j−a^j by u−a using the finite geometric-sum formula for positive and negative j. The original endpoint bounds give convergence uniformly on the annulus. Repetition removes higher multiplicities. A zero-free Laurent-analytic function has a unique dominant term at every radius by steps 3–4. On a compact annulus that exponent is constant, and factoring out its monomial leaves 1+h with uniformly |h|<1, whose geometric series supplies an analytic reciprocal. For each infinite product used below, after finitely many factors are separated, the remaining factors and their inverses converge geometrically to one. Thus cancellation of matched zeros and poles gives the Laurent-analytic quotients used below. Uniqueness of Laurent expansions makes these descriptions agree on overlapping annuli.

6. Define Θ(u)=(1−u)∏_{d≥1}(1−q^d u)(1−q^d/u)/(1−q^d)². This product converges uniformly on every closed annulus in Ω×. Its zeros are simple and exactly q^ℤ: precisely one displayed linear factor vanishes at each such point, while the product of the others is nonzero. Away from those zeros a sufficiently far tail consists of factors converging geometrically to one and has nonzero product. At u=1 the product remaining after 1−u has value one, so Θ(u)=−(u−1)+higher terms. Reindexing finite products and taking limits gives Θ(qu)=−u⁻¹Θ(u) and Θ(u⁻¹)=−u⁻¹Θ(u).

7. A Laurent-analytic function on Ω× without zeros is a monomial c u^n. Steps 2–4 show that its maximizing exponent cannot change on any compact radius interval. A single exponent n therefore maximizes at every radius. For j≠n, the inequalities |c_j|ρ^j≤|c_n|ρ^n for all ρ∈|Ω×| force c_j=0 by letting ρ approach zero or infinity along powers of |q|. The expansions on overlapping annuli agree, so this is a global monomial. Also every pole-free q-periodic Laurent-analytic function is constant, without a nonvanishing assumption: comparing coefficients in f(qu)=f(u) gives (q^j−1)c_j=0. Since |q|<1, all coefficients except c₀ vanish.

8. Let f be a nonzero q-periodic meromorphic function whose only poles are q^ℤ, with common order d>0, defined over a finite extension of F. The function g=fΘ^d is Laurent-analytic, nonzero at q^ℤ, and satisfies g(qu)=(−1)^d u⁻ᵈg(u). At radii with a unique maximizing exponent this gives n_g(|q|ρ)=n_g(ρ)−d. Choose ρ avoiding the finitely many exceptional radii in a fundamental interval; available radii include |q|^ℚ, so such a choice exists. Step 4 counts exactly d zeros in |q|ρ<|u|<ρ, with multiplicity, hence d zeros modulo q^ℤ. Choose representatives a₁,…,a_d. By step 5, h=g/∏_{i=1}^dΘ(u/a_i) is Laurent-analytic without zeros or poles, over a finite extension containing these representatives. Thus h=c u^n by step 7. Its transformation formula is h(qu)=(∏a_i)⁻¹h(u). Consequently ∏a_i=q^(−n). This proves both the zero count and product relation, including multiplicities.

9. For every natural k, the Lambert series converges in F: |d|≤1 and |1−q^d|=1, so its d-th term is bounded by |q|^d. For u∈Ω× outside q^ℤ, the bilateral series defining X(u),Y(u) converge in the complete finite extension F(u). Their positive tails are bounded by geometric multiples of |q|^n. In a negative tail, put z=q^n u; once |z|>1, both z/(1−z)² and z²/(1−z)³ have norm |z|⁻¹, again giving geometric decay. Thus the corresponding families are summable, including the unordered interpretation of the bilateral sums. These estimates are uniform on closed annuli after separating their finitely many poles and remain geometric after any fixed number of derivatives. The resulting functions have poles only at q^ℤ and are q-periodic by reindexing. Changing n to −n gives X(u⁻¹)=X(u) and Y(u⁻¹)=−Y(u)−X(u). Termwise logarithmic differentiation gives u dX/du=X+2Y.

10. On |q|<|u|<|q|⁻¹, separation of n=0 and geometric expansion give X(u)=u/(1−u)²+Σ_{j≥1}j q^j(u^j+u^(−j))/(1−q^j)−2s₁. Use the invertible formal local substitution u=exp(t) at u=1. This computes orders and coefficients in characteristic zero and does not require convergence of the exponential. Inverting 1−exp(t) gives exp(t)/(1−exp(t))²=t⁻²−1/12+t²/240−t⁴/6048+O(t⁶). Expanding exp(jt)+exp(−jt) therefore gives X=t⁻²−1/12+A t²+B t⁴+O(t⁶), where A=(1+240s₃)/240 and B=(−1+504s₅)/6048; the constant Lambert contribution 2s₁ cancels. Fixed-order coefficient sums converge by the geometric estimates of step 9. Put Z=X+1/12, and let a prime denote logarithmic differentiation u d/du=d/dt. Direct expansion gives (Z′)²−4Z³=−20A t⁻²−28B+O(t²). Thus (Z′)²−4Z³+20AZ+28B has no pole at u=1 and has constant coefficient zero. Periodicity removes every possible pole. Step 7 makes it constant, and its computed constant coefficient makes it identically zero. Substitution of Z=X+1/12 and X′=X+2Y gives Y²+XY=X³−5s₃X−(5s₃+7s₅)/12. Expanding the definitions of the invariants gives c₄=1+240s₃ and c₆=−1+504s₅.

11. For v∉q^ℤ, we have X(u)−X(v)=−v Θ(uv)Θ(u/v)/(Θ(u)²Θ(v)²). To prove this identity, the left side has double poles at q^ℤ, and its zeros include v and v⁻¹ modulo q^ℤ. If those classes coincide, invariance under u↦v²/u, whose derivative at v is −1, makes that zero at least double. Characteristic zero ensures that −1 differs from 1. Step 8 shows that these are all zeros with multiplicity. The right side has the same zeros and poles and is q-periodic by step 6. Their quotient is consequently pole-free and periodic, hence constant. At u=1 the left side has coefficient 1 in (u−1)⁻². On the right, Θ(v)Θ(v⁻¹)=−v⁻¹Θ(v)² and Θ(u)² starts with (u−1)², giving the same coefficient. The constant is one.

12. Choose s∈Ω with s²=q and put e₁=X(−1), e₂=X(s), e₃=X(−s). These parameters lie outside q^ℤ and have distinct classes: |s|=|q|^(1/2), and −1 is not a power of q. Set A₀=Θ(−1), B₀=Θ(s), C₀=Θ(−s), all nonzero. Step 11, together with Θ(−q)=Θ(−1), Θ(−1/s)=s⁻¹Θ(−s) and Θ(1/s)=−s⁻¹Θ(s), gives e₁−e₂=−C₀²/(A₀²B₀²), e₁−e₃=−B₀²/(A₀²C₀²), and e₂−e₃=s A₀²/(B₀²C₀²). Thus the e_i are distinct. Differentiating the inversion identity at these inversion-fixed parameter classes gives X+2Y=0 there. The cubic equation says that the e_i are the three roots of 4X³+X²+4a₄X+4a₆. Completing the square gives (Y+X/2)²=X³+X²/4+a₄X+a₆. Expansion of the cubic discriminant and the Weierstrass invariant definitions gives Δ(T)=16∏_{i<j}(e_i−e_j)². Substitution of the three differences yields Δ(T)=16q/(A₀B₀C₀)^4.

13. Let P=∏_{d≥1}(1−q^d). Its factors tend geometrically to one, so the product converges and is nonzero. The theta definitions, separated into even and odd powers of s, give A₀=2∏_{d≥1}(1+q^d)²/P², B₀=∏_{j≥1, j odd}(1−s^j)²/P², and C₀=∏_{j≥1, j odd}(1+s^j)²/P². Hence A₀B₀C₀=2[∏_{d≥1}(1+q^d)∏_{j≥1, j odd}(1−q^j)]²/P⁶=2/P⁶. The bracket is one because 1+q^d=(1−q^(2d))/(1−q^d), and separating P into its even and odd factors cancels everything. Geometric convergence justifies these rearrangements. Step 12 gives Δ(T)=qP²⁴=q∏_{d≥1}(1−q^d)^24≠0. The product of the 24th powers converges because |(1−q^d)^24−1|≤|q|^d. Both sides lie in F, so injectivity of F→Ω gives the identity over F. In particular T is nonsingular.

14. Define φ(u)=(X(u),Y(u)) for u∉q^ℤ and φ(u)=O for u∈q^ℤ. The cubic identity and nonzero discriminant make these nonsingular affine points. Periodicity makes φ depend only on u modulo q^ℤ, and inversion gives φ(u⁻¹)=−φ(u). For any x₀∈Ω, step 8 applied to X−x₀ gives a parameter u with X(u)=x₀; this application takes place over a finite extension containing x₀. The two roots in y of the Weierstrass equation are Y(u) and −Y(u)−x₀, realized by u and u⁻¹. This remains true when the roots coincide. Thus every affine point is in the image, and O is also in the image. The map is surjective.

15. The map is injective modulo q^ℤ. Step 11 shows that equal x-coordinates imply u/v∈q^ℤ or uv∈q^ℤ. In the second case, equality of y-coordinates requires X(v)+2Y(v)=0. Differentiating step 11 at u=v gives X(v)+2Y(v)=v Θ(v²)/Θ(v)^4. Hence equality of y-coordinates forces v²∈q^ℤ, in which case v and v⁻¹ already have the same class. This proves injectivity on classes, including the two-torsion fibers. By construction, φ(u)=O exactly when u∈q^ℤ.

16. The parametrization preserves local intersection multiplicities. At an affine image where h=X+2Y≠0, x is a local parameter on the smooth cubic and its logarithmic derivative is h≠0. At h=0, put G(x)=4x³+x²+4a₄x+4a₆. The identities h²=G(X) and X′=h give h′=G′(X)/2 after cancellation of the nonzero meromorphic function h. Since Δ≠0, G′(X)≠0 at a root of G. Therefore Y′=(h′−X′)/2=G′(X)/4≠0 there, and y is a local parameter on the cubic at that point. At u=1, step 10 gives X∼t⁻² and Y∼−t⁻³, so −x/y pulls back to t plus higher terms. The projective coordinates [X/Y:1:1/Y] consequently extend φ analytically to O, and periodicity gives the same extension at every q^m. At every point a local parameter pulls back with order one, proving preservation of intersection multiplicities.

17. Use the chord-and-tangent law for smooth Weierstrass cubics, including the rule that three line intersections counted with multiplicity sum to O; these are the geometric facts in Silverman, The Arithmetic of Elliptic Curves, second edition, Chapter III, §§2–3. For a line a x+b y+c=0 with b≠0, the pullback aX+bY+c has poles of order three exactly at q^ℤ. Step 8 gives three zero parameters with multiplicity whose product belongs to q^ℤ; step 16 identifies them with its three intersections with the cubic. A vertical line instead has poles of order two, and its two affine intersection parameters have product in q^ℤ; its third intersection is O, represented by 1. The line at infinity has intersection 3O. For φ(u),φ(v) different from O, take their secant, or their tangent if they coincide. The product relation and injectivity modulo q^ℤ show that the third intersection has parameter class (uv)⁻¹. The chord-and-tangent law and inversion give φ(u)+φ(v)=φ(uv). If either point is O, the same identity follows from periodicity. Multiplicities include tangencies and coincident intersections. Thus φ is a homomorphism with kernel exactly q^ℤ. Regard its domain as Additive Ωˣ to obtain the required additive homomorphism θ.

18. Every F-automorphism σ of Ω is isometric. For a fixed nonzero u, its restriction F(u)→F(σu) is an F-linear map between finite-dimensional normed spaces over the complete nontrivially normed field F, so it is bounded; the pinned LinearMap.continuous_of_finiteDimensional supplies continuity, equivalently boundedness here. Apply its bound to u^n and take nth roots as n tends to infinity to get |σu|≤|u|. Apply the same argument to σ⁻¹ to get equality. The assertion is immediate for u=0. Therefore σ commutes with each convergent series above and fixes q and all s_k. It follows that X(σu)=σX(u) and Y(σu)=σY(u). The point action is coordinatewise, so φ(σu)=σφ(u); this also holds on q^ℤ. Together with steps 9, 10, 13, 14 and 17, this proves every convergence, invariant, nonsingularity, surjectivity, kernel, coordinate and equivariance assertion in the statement.

## Key steps

1. Establish completeness and discrete valuation rings for finite intermediate extensions.
2. Derive annular zero counting from formal Weierstrass preparation.
3. Justify Laurent-series division and construct the theta product.
4. Prove rigidity and the periodic zero count and product relation with multiplicities.
5. Establish convergence, periodicity, inversion and logarithmic differentiation of X and Y.
6. Compute Laurent principal parts and the constant coefficient to prove the cubic equation.
7. Prove the theta difference identity.
8. Evaluate at the three two-torsion parameter classes to derive the discriminant product.
9. Prove surjectivity and injectivity modulo q^ℤ.
10. Check local parameters and pull back lines to prove the group law.
11. Prove automorphisms are isometric and deduce equivariance.

## Reference use

### local-project

Queries:
- `rg -n -i 'tate.?curve|tate.?uniform|closed annuli|q.periodic|preΨ.*torsion|torsion.*preΨ|instIsEllipticBaseChange|compl₂EDSAux_neg_two' .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions`
- `sed -n '130,315p' .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `sed -n '240,275p' .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
- `sed -n '795,825p' .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`
- `rg -n 'FiniteDimensional.complete|LinearMap.continuous_of_finiteDimensional' .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `sed -n '260,300p' .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean`
- `rg -n 'p03_odd_division_detection_68cf3476|p03_tate_uniformization_68cf3476' --glob '*.lean' .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project .humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib`
- `python3 /tmp/p03_decomposition_policy_probe.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions/Def_FLTPrelim_GaloisRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/local-references/68cf3476875a5481/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p03-policy-decomposition-14y_t8bm/results.json`
- `/tmp/p03-policy-decomposition-14y_t8bm/TypesAfterSubmission.lean`
- `/tmp/p03-policy-decomposition-14y_t8bm/TypesAfterSubmission.lean.log`
- `/tmp/p03-policy-decomposition-14y_t8bm/InstancesAfterSubmission.lean`
- `/tmp/p03-policy-decomposition-14y_t8bm/InstancesAfterSubmission.lean.log`
- `/tmp/p03-policy-decomposition-14y_t8bm/AdditionalLibraryAxioms.lean.log`
- `/tmp/p03-policy-decomposition-14y_t8bm/TargetAbsence.lean`

The snapshot supplies the exact preΨ' initial values, recurrences, coefficient-map compatibility, degree and leading-coefficient formulas, formal Weierstrass preparation, finite-dimensional completeness, and coordinatewise point action. The searched roots returned no relevant match for Tate uniformization, annular zero counting, or odd preΨ' torsion detection. Neither proposed identifier occurs in the searched libraries or the ten inspected DAGs. Fresh diagnostics confirmed clean project revision 81f093181fd6c58dc887fcae5ec8b896996f1885, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and all pinned dependency revisions. Both literal child types elaborate after import Submission in a disposable compiler copy. Instance probes confirmed multiplication of units under Additive, the elliptic-curve point group, coordinatewise Galois action, and preservation of norms by NormedAlgebra. The two type definitions and nine inspected library declarations transitively use only propext, Classical.choice, and Quot.sound. The recorded frozen_header_repair binds policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, exact omitted lines 10 and 11, original hash dd8891addb75e48583885c932518af8bc6d34438aec4e3ccd76ce6aa765e423f, derived hash 81502485ae6796527a5c4e210837b198322b438244a2f58054b94b98aef9dda9, reversible reconstruction, and a successful Lean absence probe for all 37 targets. Original sources remain unchanged. These are interface and library diagnostics, not child-proof or root-comparator acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
