# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.transfer_theta-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-transfer-theta-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `transfer_theta`
- Declaration: `Submission.p08_7d1ff633a4_transfer_theta`
- Exact Lean type: `∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (H : Subgroup G) [H.FiniteIndex] (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E₀ → Normal ℚ E₀ → E₀.fixingSubgroup.comap r ≤ H → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ a : A, A.ρ g a = a) → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ g b = b) → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ z : N, N.ρ g z = z) → ∀ φ : A →ₗ[k] B →ₗ[k] N, (∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)) → let rH := r.comp H.subtype; let AH := Rep.res H.subtype A; let BH := Rep.res H.subtype B; let NH := Rep.res H.subtype N; let φH : AH →ₗ[k] BH →ₗ[k] NH := φ; let X : Fin 3 → ModuleCat k := ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 r A), ModuleCat.of k (groupCohomology.continuousH2 r A)]; let Y : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 r B), ModuleCat.of k (groupCohomology.continuousH1 r B), ModuleCat.of k B.ρ.invariants]; let XH : Fin 3 → ModuleCat k := ![ModuleCat.of k AH.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 rH AH), ModuleCat.of k (groupCohomology.continuousH2 rH AH)]; let YH : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 rH BH), ModuleCat.of k (groupCohomology.continuousH1 rH BH), ModuleCat.of k BH.ρ.invariants]; ∃ (RX : ∀ i : Fin 3, X i →ₗ[k] XH i) (CX : ∀ i : Fin 3, XH i →ₗ[k] X i) (RY : ∀ i : Fin 3, Y i →ₗ[k] YH i) (CY : ∀ i : Fin 3, YH i →ₗ[k] Y i) (RN : groupCohomology.continuousH2 r N →ₗ[k] groupCohomology.continuousH2 rH NH) (CN : groupCohomology.continuousH2 rH NH →ₗ[k] groupCohomology.continuousH2 r N), (∀ (i : Fin 3) (x : X i), CX i (RX i x) = (H.index : k) • x) ∧ (∀ (i : Fin 3) (y : Y i), CY i (RY i y) = (H.index : k) • y) ∧ (∀ z : groupCohomology.continuousH2 r N, CN (RN z) = (H.index : k) • z) ∧ ∀ ℓ : groupCohomology.continuousH2 r N →ₗ[k] k, ∃ (Θ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i)) (ΘH : ∀ i : Fin 3, XH i →ₗ[k] Module.Dual k (YH i)), (groupCohomology.IsTheta0 r φ ℓ (Θ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Θ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Θ 2)) ∧ (groupCohomology.IsTheta0 rH φH (ℓ.comp CN) (ΘH 0) ∧ groupCohomology.IsTheta1 rH φH (ℓ.comp CN) (ΘH 1) ∧ groupCohomology.IsTheta2 rH φH (ℓ.comp CN) (ΘH 2)) ∧ (∀ Ψ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i), (groupCohomology.IsTheta0 r φ ℓ (Ψ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Ψ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Ψ 2)) → ∀ i : Fin 3, Ψ i = Θ i) ∧ (∀ (i : Fin 3) (x : X i) (y : YH i), ΘH i (RX i x) y = Θ i x (CY i y)) ∧ (∀ (i : Fin 3) (x : XH i) (y : Y i), ΘH i x (RY i y) = Θ i (CX i x) y)`

## Sibling prerequisites

- `root.normal_refinement-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
