# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1.mobius_upper_half_plane_bijection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1-pseudohyperbolic-disks-a1-disk-m-53f9f3ac68/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.level_one_valence_inequality-a1.pseudohyperbolic_disks-a1.disk_mobius_image-a1`
- Child key: `mobius_upper_half_plane_bijection`
- Declaration: `Submission.p10_17ae7b7d_phdisk_mobius_bijon`
- Exact Lean type: `∀ (a b c d : ℝ), a * d - b * c = 1 → Set.BijOn (fun z : ℂ => ((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
