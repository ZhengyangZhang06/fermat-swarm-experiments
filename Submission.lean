import Mathlib

set_option autoImplicit false

open CategoryTheory Rep Representation MonoidalCategory

namespace Submission

/-- Transfer and projection on tensor coinvariant homology have composite the subgroup index.

Transfer is the sum over right cosets, with each summand descended through representative
independence. Naturality gives chain maps, and the additive homology functor preserves their
index composite. The quotient of right cosets is used directly, so the construction does not
require a choice of transversal or normality of `H`.

The quotient and restriction APIs come from mathlib's `RepresentationTheory/Coinvariants.lean`
and `RepresentationTheory/Rep/Res.lean`; the complex and additive homology APIs come from
`RepresentationTheory/Homological/GroupHomology/Basic.lean` and
`Algebra/Homology/ShortComplex/HomologicalComplex.lean`, at the pinned revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. -/
theorem p04_ht_coinvariant_complex_transfer
    {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H]
    (C : ChainComplex (Rep k G) ℕ) (n : ℕ) :
    ∃ T : (C.coinvariantsTensorObj A).homology n →ₗ[k]
      ((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj
          (Rep.res H.subtype A)).homology n,
    ∃ P : ((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj
          (Rep.res H.subtype A)).homology n →ₗ[k]
      (C.coinvariantsTensorObj A).homology n,
    ∀ x : (C.coinvariantsTensorObj A).homology n, P (T x) = H.index • x := by
  classical
  let Q := Quotient (QuotientGroup.rightRel H)
  let : Fintype Q := Fintype.ofFinite Q
  have cardQ : Fintype.card Q = H.index := by
    rw [H.index_eq_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)
  -- The summand depends only on the right coset of the representative.
  have representative_independent (W : Rep k G) (s t : G)
      (h : QuotientGroup.rightRel H s t) :
      Coinvariants.mk (W.ρ.comp H.subtype) ∘ₗ W.ρ s =
        Coinvariants.mk (W.ρ.comp H.subtype) ∘ₗ W.ρ t := by
    ext v
    have e := Coinvariants.mk_self_apply (W.ρ.comp H.subtype)
      (⟨t * s⁻¹, QuotientGroup.rightRel_apply.mp h⟩ : H) (W.ρ s v)
    simpa [← Module.End.mul_apply, ← map_mul] using e.symm
  let summand (W : Rep k G) : Q → (W →ₗ[k] Coinvariants (W.ρ.comp H.subtype)) :=
    Quotient.lift (fun s => Coinvariants.mk (W.ρ.comp H.subtype) ∘ₗ W.ρ s)
      (representative_independent W)
  let rightMul (g : G) : Q ≃ Q :=
    { toFun := Quotient.map (fun s => s * g) (by
        intro s t h
        apply QuotientGroup.rightRel_apply.mpr
        simpa using QuotientGroup.rightRel_apply.mp h)
      invFun := Quotient.map (fun s => s * g⁻¹) (by
        intro s t h
        apply QuotientGroup.rightRel_apply.mpr
        simpa using QuotientGroup.rightRel_apply.mp h)
      left_inv := by intro q; induction q using Quotient.inductionOn; simp
      right_inv := by intro q; induction q using Quotient.inductionOn; simp }
  have summand_mul (W : Rep k G) (g : G) (q : Q) :
      summand W q ∘ₗ W.ρ g = summand W (rightMul g q) := by
    induction q using Quotient.inductionOn with | h s =>
      dsimp [summand, rightMul]
      rw [map_mul]
      rfl
  let transfer (W : Rep k G) : W.ρ.Coinvariants →ₗ[k]
      Coinvariants (W.ρ.comp H.subtype) :=
    Coinvariants.lift W.ρ (∑ q : Q, summand W q) (by
      intro g
      ext v
      simp only [LinearMap.comp_apply, LinearMap.sum_apply]
      have term (q : Q) : summand W q (W.ρ g v) = summand W (rightMul g q) v :=
        congrArg (fun f => f v) (summand_mul W g q)
      simp_rw [term]
      exact (rightMul g).sum_comp (fun q => summand W q v))
  let projection (W : Rep k G) : Coinvariants (W.ρ.comp H.subtype) →ₗ[k]
      W.ρ.Coinvariants := Coinvariants.lift _ (Coinvariants.mk W.ρ) (by
        intro h
        ext v
        exact Coinvariants.mk_self_apply W.ρ (h : G) v)
  have projection_transfer (W : Rep k G) (x : W.ρ.Coinvariants) :
      projection W (transfer W x) = H.index • x := by
    induction x using Coinvariants.induction_on with | h v =>
      change projection W ((∑ q : Q, summand W q) v) = _
      simp only [LinearMap.sum_apply, map_sum]
      have term (q : Q) : projection W (summand W q v) = Coinvariants.mk W.ρ v := by
        induction q using Quotient.inductionOn with | h s =>
          exact Coinvariants.mk_self_apply W.ρ s v
      simp_rw [term]
      simp [cardQ]
  have transfer_natural {W V : Rep k G} (f : W ⟶ V) :
      Coinvariants.map _ _ (Rep.resMap H.subtype f).hom ∘ₗ transfer W =
        transfer V ∘ₗ Coinvariants.map _ _ f.hom := by
    apply Coinvariants.hom_ext
    ext v
    change Coinvariants.map _ _ (Rep.resMap H.subtype f).hom
      ((∑ q : Q, summand W q) v) = (∑ q : Q, summand V q) (f.hom v)
    simp only [LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with | h s =>
      change Coinvariants.mk _ (f.hom (W.ρ s v)) = Coinvariants.mk _ (V.ρ s (f.hom v))
      rw [Rep.hom_comm_apply]
  have projection_natural {W V : Rep k G} (f : W ⟶ V) :
      Coinvariants.map _ _ f.hom ∘ₗ projection W =
        projection V ∘ₗ Coinvariants.map _ _ (Rep.resMap H.subtype f).hom := by
    apply Coinvariants.hom_ext
    rfl
  -- Restriction preserves the underlying tensor modules and their differentials definitionally.
  let D := C.coinvariantsTensorObj A
  let E := (((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj (Rep.res H.subtype A)
  let τ : D ⟶ E :=
    { f := fun i => ModuleCat.ofHom (transfer (A ⊗ C.X i))
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        exact transfer_natural (A ◁ C.d i j) }
  let π : E ⟶ D :=
    { f := fun i => ModuleCat.ofHom (projection (A ⊗ C.X i))
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        exact projection_natural (A ◁ C.d i j) }
  have composite : τ ≫ π = H.index • 𝟙 D := by
    ext i x
    exact projection_transfer (A ⊗ C.X i) x
  -- Functoriality and additivity pass the degreewise identity to every homology degree.
  let F := HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n
  refine ⟨(F.map τ).hom, (F.map π).hom, ?_⟩
  intro x
  have e : F.map τ ≫ F.map π = H.index • 𝟙 (F.obj D) := by
    rw [← F.map_comp, composite, F.map_nsmul, F.map_id]
  exact congrArg (fun f => f.hom x) e

end Submission
