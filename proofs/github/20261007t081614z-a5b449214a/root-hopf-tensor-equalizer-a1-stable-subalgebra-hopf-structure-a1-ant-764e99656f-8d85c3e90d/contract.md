<!-- theorem-id: fermat-p05/root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.antipode_lift-a1 -->

## Theorem `Submission.p05_hte_sshs_antipode_lift_a5b449214a`

Let k be a field, A a commutative ring equipped with a specified bialgebra structure bA over k, H a commutative Hopf k-algebra, and ι:A→H an injective bialgebra homomorphism. Suppose that for every a in A there exists b in A with ι(b)=S_H(ι(a)). Then there exists a Hopf algebra structure hA on the existing commutative ring A whose entire underlying bialgebra structure is bA and whose antipode satisfies ι(S_A(a))=S_H(ι(a)) for every a in A.

Node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.antipode_lift-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/263

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_hte_sshs_antipode_lift_a5b449214a`

```lean
∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [bA : Bialgebra k A] {H : Type*} [CommRing H] [HopfAlgebra k H] (ι : BialgHom k A H) (hι : Function.Injective ι) (hS : ∀ a : A, ∃ b : A, ι b = HopfAlgebra.antipode k (ι a)), ∃ hA : HopfAlgebra k A, hA.toHopfAlgebraStruct.toBialgebra = bA ∧ (letI : Algebra k A := hA.toHopfAlgebraStruct.toBialgebra.toAlgebra; letI : Module k A := Algebra.toModule; letI : Bialgebra k A := hA.toHopfAlgebraStruct.toBialgebra; letI : HopfAlgebra k A := hA; ∀ a : A, ι (HopfAlgebra.antipode k a) = HopfAlgebra.antipode k (ι a))
```

### Frozen project context

`Fermat/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean` at `2fdd42759f4ab17640ac773289b521dd69d4b26e` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.hopfKer_eq_of_surjective_of_ker_eq_span
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    {B : Type w} [CommRing B] [Bialgebra k B] (q : H →ₐc[k] B) (hq : Function.Surjective q)
    (hker : RingHom.ker (q : H →+* B) =
      Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}) :
    HopfAlgebra.hopfKer q = K := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1`
- Child DAG node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.antipode_lift-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. For each a in A, the hypothesis supplies b in A with ι(b)=S_H(ι(a)); injectivity of ι makes b unique. Define S_A(a) to be this unique b. By definition, ι(S_A(a))=S_H(ι(a)) for every a.
2. The map S_A is k-linear. For a,a′ in A, the images under ι of S_A(a+a′) and S_A(a)+S_A(a′) are equal because both ι and S_H preserve sums. For c in k, the images of S_A(c a) and c S_A(a) are equal because both maps preserve k-scalars. Also the images of S_A(0) and 0 are zero. Injectivity of ι gives each asserted equality in A, defining a linear endomorphism S_A for the module structure of bA.
3. Fix a in A and write its existing coproduct as a finite sum Δ_A(a)=Σ_j x_j⊗y_j, possible because pure tensors generate A⊗_k A. Since ι is a bialgebra homomorphism, Δ_H(ι(a))=Σ_j ι(x_j)⊗ι(y_j) and ε_H(ι(a))=ε_A(a). Its algebra-homomorphism properties also give ι(ε_A(a)1_A)=ε_A(a)1_H.
4. Apply ι to the left antipode expression Σ_j S_A(x_j)y_j. Its image is Σ_j S_H(ι(x_j))ι(y_j), by multiplicativity, additivity, and step 1. The left antipode identity in H identifies this sum with ε_H(ι(a))1_H=ι(ε_A(a)1_A). Injectivity of ι proves Σ_j S_A(x_j)y_j=ε_A(a)1_A. Using the pure-tensor formulas for multiplication and tensor maps, this is m_A(S_A⊗id_A)Δ_A(a)=ε_A(a)1_A.
5. Similarly, the image of Σ_j x_j S_A(y_j) is Σ_j ι(x_j)S_H(ι(y_j)). The right antipode identity in H makes this ε_H(ι(a))1_H=ι(ε_A(a)1_A). Injectivity proves m_A(id_A⊗S_A)Δ_A(a)=ε_A(a)1_A. Since a was arbitrary, steps 4–5 establish both antipode axioms as equalities of linear maps.
6. Extend the specified structure bA by the linear endomorphism S_A and the two identities just proved. This yields hA:HopfAlgebra k A with its entire underlying bialgebra structure exactly bA, not merely an isomorphic bialgebra. Its antipode is the chosen S_A, so the compatibility asserted in the conclusion is precisely step 1.

## Key steps

1. Use range stability and injectivity to define the unique lifted antipode.
2. Prove linearity by applying the injective bialgebra homomorphism.
3. Expand the existing coproduct and use preservation of comultiplication and counit.
4. Transfer the left and right antipode identities from H by injectivity.
5. Extend exactly the specified bialgebra structure and retain antipode compatibility.

## Reference use

### local-project

Queries:
- `injective|Injective|Subalgebra|Subcoalgebra|subalgebra|of_injective`
- `exists_leftInverse|leftInverse|map_injective|range_map|span_tmul|range.*[Tt]ensor|lift.*[Bb]ialgebra|[Ii]njective.*[Hh]opf|[Ss]ubalgebra.*[Bb]ialgebra`
- `injective.*hopf|hopf.*injective|stable.*[Ss]ubalgebra|[Ss]ubalgebra.*[Hh]opf|[Ss]ubalgebra.*[Bb]ialgebra|[Bb]ialgebra.*[Ss]ubalgebra`
- `p05_hte_sshs_bialgebra_restriction_a5b449214a|p05_hte_sshs_antipode_lift_a5b449214a`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Map.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Bialgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Bialgebra/Hom.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1/decomposition-sshs-diagnostics/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1/decomposition-sshs-diagnostics/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1/decomposition-sshs-diagnostics/CheckComposition.lean`

The snapshot supplies LinearMap.exists_leftInverse_of_injective, TensorProduct.range_map_eq_span_tmul, bialgebra constructors, and the two antipode identities. Searches found no matching subalgebra restriction or injective antipode-lifting theorem, and neither proposed identifier is reserved in the current DAG. Project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and all nine dependencies passed clean-pin checks. Both literal child types elaborate after import Submission in the derived challenge and solution contexts. Nine explicit instance probes passed; the antipode interface explicitly installs its new underlying bialgebra. An anonymous implication check verified that the two interfaces compose to the exact parent type. Nine infrastructure axiom closures contain only propext, Classical.choice and Quot.sound. The matching compiler-copy policy digest was checked; only listed lines 10–11 were omitted, reversible original/build hashes were validated, and Lean confirmed all 13 omitted targets absent. Protected inputs remain unchanged. These are decomposition diagnostics, not comparator acceptance of either child theorem.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/353

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
