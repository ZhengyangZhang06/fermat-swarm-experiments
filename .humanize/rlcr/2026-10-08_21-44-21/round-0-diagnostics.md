# Round 0 Local Diagnostic Record

This is an incomplete local proof attempt, not a solution or an accepted helper theorem. The exact-goal attempt exits 1. All displayed Lean was run only in a disposable directory and was not added to Submission.lean.

## Exact-goal attempt

```lean
import AcceptedDependencies
example :
  ∀ (F Ω : Type) [NormedField F] [CharZero F] [CompleteSpace F] [NormedField Ω] [CharZero Ω] [DecidableEq Ω] [NormedAlgebra F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω], (∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → (∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → (∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = r ^ n) → ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 → let s : ℕ → F := fun k => ∑' d : ℕ, ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1)); let T : WeierstrassCurve F := ⟨1, 0, 0, -5 * s 3, -(5 * s 3 + 7 * s 5) / 12⟩; let qΩ : Ω := algebraMap F Ω q; let X : Ω → Ω := fun u => (∑' n : ℤ, qΩ ^ n * u / (1 - qΩ ^ n * u) ^ 2) - 2 * algebraMap F Ω (s 1); let Y : Ω → Ω := fun u => (∑' n : ℤ, (qΩ ^ n * u) ^ 2 / (1 - qΩ ^ n * u) ^ 3) + algebraMap F Ω (s 1); (∀ k : ℕ, Summable (fun d : ℕ => ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1)))) ∧ Multipliable (fun d : ℕ => (1 - q ^ (d + 1)) ^ 24) ∧ T.c₄ = 1 + 240 * s 3 ∧ T.c₆ = -1 + 504 * s 5 ∧ T.Δ = q * (∏' d : ℕ, (1 - q ^ (d + 1)) ^ 24) ∧ T.Δ ≠ 0 ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → Summable (fun n : ℤ => qΩ ^ n * (u : Ω) / (1 - qΩ ^ n * (u : Ω)) ^ 2) ∧ Summable (fun n : ℤ => (qΩ ^ n * (u : Ω)) ^ 2 / (1 - qΩ ^ n * (u : Ω)) ^ 3)) ∧ ∃ θ : Additive Ωˣ →+ (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Point, Function.Surjective θ ∧ (∀ u : Ωˣ, θ (Additive.ofMul u) = 0 ↔ ∃ m : ℤ, (u : Ω) = qΩ ^ m) ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → ∃ h : (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Nonsingular (X (u : Ω)) (Y (u : Ω)), θ (Additive.ofMul u) = WeierstrassCurve.Affine.Point.some (X (u : Ω)) (Y (u : Ω)) h) ∧ ∀ (σ : Ω ≃ₐ[F] Ω) (u : Ωˣ), θ (Additive.ofMul (Units.map σ.toMonoidHom u)) = σ • θ (Additive.ofMul u) := by
  intro F Ω _ _ _ _ _ _ _ _ _ hF hΩ _hdisc q hq0 hq1 s T qΩ X Y
  have hsum := Submission.p03_tu_lambert_summable_68cf3476 F hF q hq1
  have heuler := (Submission.p03_tu_euler_product_powers_68cf3476 F hF q hq1).2.2 24
  have hc4 : T.c₄ = 1 + 240 * s 3 := by
    dsimp only [T, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hc6 : T.c₆ = -1 + 504 * s 5 := by
    dsimp only [T, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    field_simp
    ring
  have hbilateral := Submission.p03_tu_bilateral_summable_68cf3476 F Ω hΩ q hq0 hq1
  suffices hcore : T.Δ = q * (∏' d : ℕ, (1 - q ^ (d + 1)) ^ 24) ∧ (∃ θ : Additive Ωˣ →+ (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Point, Function.Surjective θ ∧ (∀ u : Ωˣ, θ (Additive.ofMul u) = 0 ↔ ∃ m : ℤ, (u : Ω) = qΩ ^ m) ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → ∃ h : (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Nonsingular (X (u : Ω)) (Y (u : Ω)), θ (Additive.ofMul u) = WeierstrassCurve.Affine.Point.some (X (u : Ω)) (Y (u : Ω)) h)) by
    obtain ⟨hdelta, θ, hsurj, hker, hcoords⟩ := hcore
    have hnonzero : T.Δ ≠ 0 := by
      rw [hdelta]
      exact mul_ne_zero (norm_pos_iff.mp hq0) heuler.2.2
    refine ⟨hsum, heuler.1, hc4, hc6, hdelta, hnonzero, hbilateral,
      θ, hsurj, hker, hcoords, ?_⟩
    intro σ u
    let uσ := Units.map σ.toMonoidHom u
    have hσQ : σ qΩ = qΩ := σ.commutes q
    have hpower : (∃ m : ℤ, (uσ : Ω) = qΩ ^ m) ↔
        (∃ m : ℤ, (u : Ω) = qΩ ^ m) := by
      constructor
      · rintro ⟨m, hm⟩
        change σ (u : Ω) = qΩ ^ m at hm
        refine ⟨m, σ.injective ?_⟩
        simpa only [map_zpow₀, hσQ] using hm
      · rintro ⟨m, hm⟩
        refine ⟨m, ?_⟩
        change σ (u : Ω) = qΩ ^ m
        rw [hm, map_zpow₀, hσQ]
    change θ (Additive.ofMul uσ) = σ • θ (Additive.ofMul u)
    by_cases hu : ∃ m : ℤ, (u : Ω) = qΩ ^ m
    · rw [(hker uσ).2 (hpower.mpr hu), (hker u).2 hu, smul_zero]
    · have huσ : ¬ ∃ m : ℤ, (uσ : Ω) = qΩ ^ m := fun h => hu (hpower.mp h)
      obtain ⟨h, himage⟩ := hcoords u hu
      obtain ⟨hσ, himageσ⟩ := hcoords uσ huσ
      have hsym := Submission.p03_tu_coordinate_symmetries_68cf3476
        F Ω hΩ q hq0 hq1 (s 1) u hu
      obtain ⟨hx, hy⟩ := hsym.2.2.2.2 σ
      rw [himageσ, himage]
      simp only [WeierstrassCurve.Affine.Point.algEquiv_smul_def,
        WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
```

## Compiler output (exit 1)

```text
AssemblyAttempt.lean:3:1688: error: unsolved goals
F Ω : Type
inst✝⁸ : NormedField F
inst✝⁷ : CharZero F
inst✝⁶ : CompleteSpace F
inst✝⁵ : NormedField Ω
inst✝⁴ : CharZero Ω
inst✝³ : DecidableEq Ω
inst✝² : NormedAlgebra F Ω
inst✝¹ : IsAlgClosed Ω
inst✝ : Algebra.IsAlgebraic F Ω
hF : ∀ (x y : F), ‖x + y‖ ≤ max ‖x‖ ‖y‖
hΩ : ∀ (x y : Ω), ‖x + y‖ ≤ max ‖x‖ ‖y‖
_hdisc : ∃ r, 0 < r ∧ r < 1 ∧ ∀ (x : F), x ≠ 0 → ∃ n, ‖x‖ = r ^ n
q : F
hq0 : 0 < ‖q‖
hq1 : ‖q‖ < 1
s : ℕ → F := fun k => ∑' (d : ℕ), ↑(d + 1) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1))
T : WeierstrassCurve F := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -5 * s 3, a₆ := -(5 * s 3 + 7 * s 5) / 12 }
qΩ : Ω := (algebraMap F Ω) q
X : Ω → Ω := fun u => ∑' (n : ℤ), qΩ ^ n * u / (1 - qΩ ^ n * u) ^ 2 - 2 * (algebraMap F Ω) (s 1)
Y : Ω → Ω := fun u => ∑' (n : ℤ), (qΩ ^ n * u) ^ 2 / (1 - qΩ ^ n * u) ^ 3 + (algebraMap F Ω) (s 1)
hsum : ∀ (k : ℕ), Summable fun d => ↑(d + 1) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1))
heuler :
  (Multipliable fun d => (1 - q ^ (d + 1)) ^ 24) ∧
    ∏' (d : ℕ), (1 - q ^ (d + 1)) ^ 24 = (∏' (d : ℕ), (1 - q ^ (d + 1))) ^ 24 ∧ ∏' (d : ℕ), (1 - q ^ (d + 1)) ^ 24 ≠ 0
hc4 : T.c₄ = 1 + 240 * s 3
hc6 : T.c₆ = -1 + 504 * s 5
hbilateral :
  have qΩ := (algebraMap F Ω) q;
  ∀ (u : Ωˣ),
    (¬∃ m, ↑u = qΩ ^ m) →
      (Summable fun n => qΩ ^ n * ↑u / (1 - qΩ ^ n * ↑u) ^ 2) ∧
        Summable fun n => (qΩ ^ n * ↑u) ^ 2 / (1 - qΩ ^ n * ↑u) ^ 3
⊢ T.Δ = q * ∏' (d : ℕ), (1 - q ^ (d + 1)) ^ 24 ∧
    ∃ θ,
      Function.Surjective ⇑θ ∧
        (∀ (u : Ωˣ), θ (Additive.ofMul u) = 0 ↔ ∃ m, ↑u = qΩ ^ m) ∧
          ∀ (u : Ωˣ),
            (¬∃ m, ↑u = qΩ ^ m) →
              ∃ (h : (T.toAffine.baseChange Ω).Nonsingular (X ↑u) (Y ↑u)),
                θ (Additive.ofMul u) = WeierstrassCurve.Affine.Point.some (X ↑u) (Y ↑u) h
```

## Conditional assembly check

The following anonymous diagnostic assumes the still-unproved conjunction explicitly and tests only assembly. It exits 0 with no output under warningAsError=true. Its extra antecedent makes it weaker than the requested theorem, so it must never be catalogued as that theorem.

```lean
import AcceptedDependencies
example :
  ∀ (F Ω : Type) [NormedField F] [CharZero F] [CompleteSpace F] [NormedField Ω] [CharZero Ω] [DecidableEq Ω] [NormedAlgebra F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω], (∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → (∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → (∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = r ^ n) → ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 → let s : ℕ → F := fun k => ∑' d : ℕ, ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1)); let T : WeierstrassCurve F := ⟨1, 0, 0, -5 * s 3, -(5 * s 3 + 7 * s 5) / 12⟩; let qΩ : Ω := algebraMap F Ω q; let X : Ω → Ω := fun u => (∑' n : ℤ, qΩ ^ n * u / (1 - qΩ ^ n * u) ^ 2) - 2 * algebraMap F Ω (s 1); let Y : Ω → Ω := fun u => (∑' n : ℤ, (qΩ ^ n * u) ^ 2 / (1 - qΩ ^ n * u) ^ 3) + algebraMap F Ω (s 1); (T.Δ = q * (∏' d : ℕ, (1 - q ^ (d + 1)) ^ 24) ∧ (∃ θ : Additive Ωˣ →+ (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Point, Function.Surjective θ ∧ (∀ u : Ωˣ, θ (Additive.ofMul u) = 0 ↔ ∃ m : ℤ, (u : Ω) = qΩ ^ m) ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → ∃ h : (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Nonsingular (X (u : Ω)) (Y (u : Ω)), θ (Additive.ofMul u) = WeierstrassCurve.Affine.Point.some (X (u : Ω)) (Y (u : Ω)) h))) → ((∀ k : ℕ, Summable (fun d : ℕ => ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1)))) ∧ Multipliable (fun d : ℕ => (1 - q ^ (d + 1)) ^ 24) ∧ T.c₄ = 1 + 240 * s 3 ∧ T.c₆ = -1 + 504 * s 5 ∧ T.Δ = q * (∏' d : ℕ, (1 - q ^ (d + 1)) ^ 24) ∧ T.Δ ≠ 0 ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → Summable (fun n : ℤ => qΩ ^ n * (u : Ω) / (1 - qΩ ^ n * (u : Ω)) ^ 2) ∧ Summable (fun n : ℤ => (qΩ ^ n * (u : Ω)) ^ 2 / (1 - qΩ ^ n * (u : Ω)) ^ 3)) ∧ ∃ θ : Additive Ωˣ →+ (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Point, Function.Surjective θ ∧ (∀ u : Ωˣ, θ (Additive.ofMul u) = 0 ↔ ∃ m : ℤ, (u : Ω) = qΩ ^ m) ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → ∃ h : (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Nonsingular (X (u : Ω)) (Y (u : Ω)), θ (Additive.ofMul u) = WeierstrassCurve.Affine.Point.some (X (u : Ω)) (Y (u : Ω)) h) ∧ ∀ (σ : Ω ≃ₐ[F] Ω) (u : Ωˣ), θ (Additive.ofMul (Units.map σ.toMonoidHom u)) = σ • θ (Additive.ofMul u)) := by
  intro F Ω _ _ _ _ _ _ _ _ _ hF hΩ _hdisc q hq0 hq1 s T qΩ X Y hcore
  have hsum := Submission.p03_tu_lambert_summable_68cf3476 F hF q hq1
  have heuler := (Submission.p03_tu_euler_product_powers_68cf3476 F hF q hq1).2.2 24
  have hc4 : T.c₄ = 1 + 240 * s 3 := by
    dsimp only [T, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hc6 : T.c₆ = -1 + 504 * s 5 := by
    dsimp only [T, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    field_simp
    ring
  have hbilateral := Submission.p03_tu_bilateral_summable_68cf3476 F Ω hΩ q hq0 hq1
  obtain ⟨hdelta, θ, hsurj, hker, hcoords⟩ := hcore
  have hnonzero : T.Δ ≠ 0 := by
    rw [hdelta]
    exact mul_ne_zero (norm_pos_iff.mp hq0) heuler.2.2
  refine ⟨hsum, heuler.1, hc4, hc6, hdelta, hnonzero, hbilateral,
    θ, hsurj, hker, hcoords, ?_⟩
  intro σ u
  let uσ := Units.map σ.toMonoidHom u
  have hσQ : σ qΩ = qΩ := σ.commutes q
  have hpower : (∃ m : ℤ, (uσ : Ω) = qΩ ^ m) ↔
      (∃ m : ℤ, (u : Ω) = qΩ ^ m) := by
    constructor
    · rintro ⟨m, hm⟩
      change σ (u : Ω) = qΩ ^ m at hm
      refine ⟨m, σ.injective ?_⟩
      simpa only [map_zpow₀, hσQ] using hm
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      change σ (u : Ω) = qΩ ^ m
      rw [hm, map_zpow₀, hσQ]
  change θ (Additive.ofMul uσ) = σ • θ (Additive.ofMul u)
  by_cases hu : ∃ m : ℤ, (u : Ω) = qΩ ^ m
  · rw [(hker uσ).2 (hpower.mpr hu), (hker u).2 hu, smul_zero]
  · have huσ : ¬ ∃ m : ℤ, (uσ : Ω) = qΩ ^ m := fun h => hu (hpower.mp h)
    obtain ⟨h, himage⟩ := hcoords u hu
    obtain ⟨hσ, himageσ⟩ := hcoords uσ huσ
    have hsym := Submission.p03_tu_coordinate_symmetries_68cf3476
      F Ω hΩ q hq0 hq1 (s 1) u hu
    obtain ⟨hx, hy⟩ := hsym.2.2.2.2 σ
    rw [himageσ, himage]
    simp only [WeierstrassCurve.Affine.Point.algEquiv_smul_def,
      WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx, hy⟩
```
