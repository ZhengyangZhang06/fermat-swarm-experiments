# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.full_level_quotient-a1.full_level_pullback-a1.pullback_point_equivalence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1-full-level-pullback-a1-pullback-point-equivalence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.full_level_quotient-a1.full_level_pullback-a1`
- Child key: `pullback_point_equivalence`
- Declaration: `Submission.p07_flp_point_equiv_857cd4d38c`
- Exact Lean type: `∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) (ET : CerednikDrinfeld.QM.FakeEllipticCurve Λ N T) (g : Quiver.Hom ET.A E.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia φ E ET g → ∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))), let tS := CategoryTheory.CategoryStruct.comp t (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)); ∃ B : NeronModelInfra.SchemeHomOver t ET.f ≃ NeronModelInfra.SchemeHomOver tS E.f, (∀ P : NeronModelInfra.SchemeHomOver t ET.f, (B P).1 = CategoryTheory.CategoryStruct.comp P.1 g) ∧ (∀ P Q : NeronModelInfra.SchemeHomOver t ET.f, B (ET.L.mul t P Q) = E.L.mul tS (B P) (B Q)) ∧ B (ET.L.one t) = E.L.one tS ∧ (∀ (k : ℕ) (P : NeronModelInfra.SchemeHomOver t ET.f), B (CerednikDrinfeld.QM.nsmulPt ET.L t k P) = CerednikDrinfeld.QM.nsmulPt E.L tS k (B P)) ∧ (∀ (x : ↥Λ) (P : NeronModelInfra.SchemeHomOver t ET.f), B (CerednikDrinfeld.QM.pushPt (ET.act x) (ET.act_over x) P) = CerednikDrinfeld.QM.pushPt (E.act x) (E.act_over x) (B P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
