# Final proof of `CuspForm.span_heckeTLin_eigen_eq_top`

## Statement and assumptions

For every natural number `M` with `[NeZero M]`, let
`V = CuspForm (CongruenceSubgroup.Gamma0 M) 2`, with its existing complex vector-space structure. Let `E` be the set of all `v : V` such that, for every natural number `ℓ`, every proof `hℓ : ℓ.Prime`, and every proof `hℓM : ¬ ℓ ∣ M`, there exists `c : ℂ` with
`CuspForm.heckeTLin 2 hℓ hℓM v = c • v`.
The conclusion is `Submodule.span ℂ E = ⊤`. Membership in `E` does not require a nonzero vector. No assumption on the dimension, an inner product, or a chosen eigenbasis is added to the frozen statement.

## Accepted dependencies actually used

The root proof uses exactly these three accepted project declarations, with their full hypotheses:

1. `Submission.f036cc6b1f_finite_dimensional`: for every natural `M` with `[NeZero M]`, `FiniteDimensional ℂ V`. Accepted candidate: `a7d4d6f75e980b40c4a8288c5d71d6b5867e2dd5`.
2. `Submission.f036cc6b1f_petersson_core`: for every natural `M` with `[NeZero M]`, there exists `B : InnerProductSpace.Core ℂ V` such that for every natural `p`, every `hp : p.Prime`, every `hpM : ¬ p ∣ M`, and all `f g : V`,
   `B.inner (CuspForm.heckeTLin 2 hp hpM f) g = B.inner f (CuspForm.heckeTLin 2 hp hpM g)`.
   The core includes positive definiteness and the Hermitian and linearity laws. Accepted candidate: `e2d1de044f6143bb7ba3c165a56c7944b4a7b02f`.
3. `Submission.f036cc6b1f_hecke_commute`: for every natural `M` with `[NeZero M]`, natural numbers `p r`, proofs `hp : p.Prime`, `hr : r.Prime`, `hpM : ¬ p ∣ M`, and `hrM : ¬ r ∣ M`,
   `(CuspForm.heckeTLin 2 hp hpM).comp (CuspForm.heckeTLin 2 hr hrM) = (CuspForm.heckeTLin 2 hr hrM).comp (CuspForm.heckeTLin 2 hp hpM)`.
   Accepted candidate: `10d8ede77769076cd2a05b10ec37b7dee89461f6`.

These are proved declarations, not temporary assumptions. Their accepted transitive dependencies are retained in the integrated source. The adjacent `root-child-interface-audit.json` records the accepted candidate and declaration hashes for all 32 children. The implementation adds no new named helper theorem.

## Complete argument matching the Lean proof

1. Fix `M` and `[NeZero M]`. Install the finite-dimensionality instance from dependency 1. Obtain the positive-definite core `B` and the symmetry identities from dependency 2. Use `InnerProductSpace.Core.toNormedAddCommGroup` to equip the existing additive group of `V` with the norm determined by `B`, and `InnerProductSpace.ofCore` to equip it with the corresponding complex inner-product-space structure. The inner product is precisely `B.inner`. These are local structures used to apply the library theorem; the underlying vectors, addition, complex scalar multiplication, and Hecke endomorphisms are unchanged. No compatibility with an independently supplied topology is needed because the target is an algebraic span equality.

2. Define the index type `I = {p : ℕ // p.Prime ∧ ¬ p ∣ M}` and the family of complex-linear endomorphisms `T p = CuspForm.heckeTLin 2 p.property.1 p.property.2`. For every `p : I`, dependency 2 states exactly that `T p` is symmetric for the local inner product: for all `f,g`, the inner products of `T p f` with `g` and of `f` with `T p g` are equal.

3. For `p,r : I`, dependency 3 gives equality of the two compositions. Multiplication in `Module.End ℂ V` is composition, so this is `Commute (T p) (T r)`. It holds for all pairs and hence supplies the pairwise-commutation hypothesis, which only requests it for distinct indices.

4. Apply the pinned library theorem `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`. Its hypotheses are an `RCLike` scalar field, a finite-dimensional inner product space, a family of symmetric linear endomorphisms indexed by an arbitrary type, and pairwise commutation. Here the scalar field is `ℂ`, and steps 1–3 verify the remaining hypotheses. The theorem gives
   `⨆ χ : I → ℂ, ⨅ p : I, Module.End.eigenspace (T p) (χ p) = ⊤`.
   Thus the supremum of all joint eigenspaces is the whole space. There is no finiteness assumption on `I`, and no enumeration or truncation of the good primes is used.

5. Fix a function `χ : I → ℂ` and a vector `v` in its joint eigenspace. Membership in the infimum implies that `v` belongs to the eigenspace of `T p` for every `p : I`. To prove `v ∈ E`, take arbitrary `ℓ`, `hℓ`, and `hℓM` as quantified in the frozen target, and form the subtype element `p = ⟨ℓ, hℓ, hℓM⟩`. The eigenspace-membership identity `Module.End.mem_eigenspace_iff` gives
   `CuspForm.heckeTLin 2 hℓ hℓM v = χ p • v`.
   Choosing `c = χ p` supplies the required existential witness. Because the subtype element is built from the very proofs supplied in this target, no assumption about a choice of primality or nondivisibility witnesses is needed.

6. By step 5, each vector in each joint eigenspace belongs to `E`, and hence to `Submodule.span ℂ E` by `Submodule.subset_span`. Therefore every joint eigenspace is contained in that span. The least-upper-bound property (`iSup_le`) implies that their supremum is contained in it. Replacing the supremum by `⊤` using step 4 yields `⊤ ≤ Submodule.span ℂ E`. The opposite inclusion holds for every submodule, so `top_unique` proves the asserted equality. This argument also covers the zero-dimensional case and an empty index type without additional assumptions.

## Library provenance and relationship to the reviewed history

The finite-dimensionality, Petersson construction, and commutation obligations were settled in the accepted child DAG. The older root scaffold and `natural-proof-v3.md` describe their mathematical development and a dimension-induction explanation of simultaneous diagonalization. They remain historical records. The root implementation calls the three accepted interfaces above and the existing arbitrary-family joint-eigenspace theorem. It does not introduce another eigenbasis or induction helper, nor does it leave a geometric or analytic step to be proved later.

The following are existing pinned mathlib results, not newly invented helpers:

The frozen `Definitions.Def_ModularForm_HeckeOperatorForms` import already reaches `Mathlib` through the unchanged `Theorems/Thm_ModularForm_mdifferentiable_heckeT.lean` and other operator wrappers. Thus these library calls require no addition to the frozen Submission header.

- `Mathlib/Analysis/InnerProductSpace/Defs.lean:470` constructs the normed additive group from the positive-definite core; the same file defines `InnerProductSpace.ofCore` at line 569.
- `Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean:121` proves `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute` for arbitrary index types. Its proof uses symmetric-operator semisimplicity and the commuting-family generalized-eigenspace decomposition; it does not reference cusp forms or this root theorem.
- `Mathlib/LinearAlgebra/Eigenspace/Basic.lean:449` supplies `Module.End.mem_eigenspace_iff`, equating eigenspace membership with the required scalar equation.
- `Submodule.mem_iInf`, `Submodule.subset_span`, `iSup_le`, and `top_unique` are the ordinary submodule and order interfaces used in the final inclusion argument.

## Reference use

`reference_use` contains exactly one source entry:

- **source:** `local-project`
  **snapshot:** `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb`
  **manifest:** `manifest.json` in that directory; project commit `61b5f85556ac71631ccad822e0694511234f7132`, mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. Both snapshot Git revisions and tracked-clean statuses, and the installed mathlib revision/status, were checked against this manifest.
  **queries and findings:** `rg -n 'heckeT.*(comm|symm|adjoint)|FiniteDimensional.*CuspForm|InnerProductSpace.*CuspForm'` over `project/Definitions` and `mathlib/Mathlib/NumberTheory/ModularForms` returned no matches (exit 1). `rg -n 'toNormedAddCommGroup|def ofCore|mem_eigenspace_iff|iSup_iInf_eq_top_of_commute'` over `mathlib/Mathlib/Analysis/InnerProductSpace` and `mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean` located the constructors and spectral interfaces above. `JointEigenspace.lean` was inspected, including its complete arbitrary-family theorem. The snapshot's `project/Definitions/Def_ModularForm_HeckeOperatorForms.lean` defines the exact bundled `CuspForm.heckeTLin`; the corresponding workspace source was inspected and remains unchanged. No network search or other reference corpus was used. Compilation, frozen-interface checks, and transitive axiom checks are required separately; this prose does not substitute for the configured comparator or the outer controller's independent review.