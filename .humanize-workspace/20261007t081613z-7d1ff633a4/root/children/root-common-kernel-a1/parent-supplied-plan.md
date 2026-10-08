# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.common_kernel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/nodes/root-common-kernel-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `common_kernel`
- Declaration: `Submission.p08_7d1ff633a4_common_kernel`
- Exact Lean type: `∀ {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (S : Subgroup (ExtCitation.primeLocalGaloisGroup q)) (U : Subgroup S) (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M], (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap ((ExtCitation.primeLocalToGlobal q).comp S.subtype) ≤ U) → (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : S, ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m) → ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧ Normal ℚ E ∧ E.fixingSubgroup.comap ((ExtCitation.primeLocalToGlobal q).comp S.subtype) ≤ U ∧ (∀ s : S, ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s ∈ E.fixingSubgroup → (∀ m : M, M.ρ s m = m) ∧ (∀ d : M.dualTwist (((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q)).comp S.subtype), (M.dualTwist (((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q)).comp S.subtype)).ρ s d = d) ∧ (∀ a : Rep.res S.subtype (groupCohomology.ofChar (k := ZMod p) ((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q))), (Rep.res S.subtype (groupCohomology.ofChar (k := ZMod p) ((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q)))).ρ s a = a))`

## Sibling prerequisites

- `root.normal_refinement-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
