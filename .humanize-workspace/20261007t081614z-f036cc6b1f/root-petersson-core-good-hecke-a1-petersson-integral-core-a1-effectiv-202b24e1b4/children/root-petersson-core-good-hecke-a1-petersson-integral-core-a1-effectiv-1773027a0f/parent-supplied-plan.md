# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.integral_of_equidecomposition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-effectiv-1773027a0f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1`
- Child key: `integral_of_equidecomposition`
- Declaration: `Submission.f036cc6b1f_pic_dt_integral_of_equidecomposition`
- Exact Lean type: `∀ (α ι : Type) [MeasurableSpace α] [Countable ι] (μ : MeasureTheory.Measure α) (E F : Set α) (A B : ι → Set α) (T : ι → α → α), MeasurableSet E → MeasurableSet F → (∀ i, MeasurableSet (A i)) → (∀ i, MeasurableSet (B i)) → Pairwise (fun i j => Disjoint (A i) (A j)) → Pairwise (fun i j => Disjoint (B i) (B j)) → (∀ᵐ x ∂μ, x ∈ E ↔ x ∈ ⋃ i, A i) → (∀ᵐ x ∂μ, x ∈ F ↔ x ∈ ⋃ i, B i) → (∀ i, MeasurableEmbedding (T i)) → (∀ i, MeasureTheory.MeasurePreserving (T i) μ μ) → (∀ i, T i '' A i = B i) → ∀ φ : α → ℂ, MeasureTheory.StronglyMeasurable φ → (∀ i, ∀ x ∈ A i, φ (T i x) = φ x) → MeasureTheory.IntegrableOn φ E μ → MeasureTheory.IntegrableOn φ F μ ∧ MeasureTheory.integral (μ.restrict E) φ = MeasureTheory.integral (μ.restrict F) φ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
