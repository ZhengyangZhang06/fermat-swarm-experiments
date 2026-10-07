# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scalar_common_ray_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-parabolic-a1-primitive-cusp-limit-a1-pcl-scalar-common-1da09434eb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1`
- Child key: `pcl_scalar_common_ray_limit`
- Declaration: `Submission.p02_es_177ebb5a_pcl_scalar_common_ray_limit`
- Exact Lean type: `∀ (n : ℕ) (a : ℝ) (H G : ℂ → ℂ), 0 < a → ContinuousOn G {z : ℂ | 0 < z.im} → (∀ z : ℂ, 0 < z.im → HasDerivAt H (G z) z) → (∀ B : ℝ, 0 < B → ∃ C Y : ℝ, 0 ≤ C ∧ 1 ≤ Y ∧ ∀ z : ℂ, |z.re| ≤ B → Y ≤ z.im → ‖G z‖ ≤ C * (1 + z.im) ^ n * Real.exp (-a * z.im)) → ∃ A : ℂ, ∀ x : ℝ, Filter.Tendsto (fun y : ℝ => H ((x : ℂ) + (y : ℂ) * Complex.I)) Filter.atTop (nhds A)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
