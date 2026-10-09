<!-- theorem-id: fermat-p05/root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1 -->

## Theorem `Submission.p05_ptm_split_of_unit_minor_a5b449214a`

Let R be a commutative ring, M an R-module, and n,p,d natural numbers. Let P be an n-by-p matrix over R and π:R^n→M a surjective R-linear map with ker π=im(P). Suppose rows:Fin d↪Fin n and cols:Fin d↪Fin p select a submatrix B whose determinant is a unit. Suppose every minor selected by embeddings Fin(d+1)↪Fin n and Fin(d+1)↪Fin p has determinant zero. Then there exists an R-linear map s:M→R^n with π∘s=id_M. No nontriviality or positivity assumptions are imposed.

Node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/253

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/304, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/305

## Lean problem

Declaration: `Submission.p05_ptm_split_of_unit_minor_a5b449214a`

```lean
∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (n p d : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M) (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin) (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p) (_hunit : IsUnit (Matrix.det (P.submatrix rows cols))) (_hnext : ∀ (rows' : Fin (d + 1) ↪ Fin n) (cols' : Fin (d + 1) ↪ Fin p), Matrix.det (P.submatrix rows' cols') = 0), ∃ s : M →ₗ[R] (Fin n → R), π.comp s = LinearMap.id
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

- Parent DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1`
- Child DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write F=R^n and G=R^p. The row embedding identifies the row index set with the disjoint union of Fin d and its complementary set I; the column embedding similarly gives Fin d and its complementary set J. The identifications send the left summands to the specified embeddings and the right summands to the complementary indices. They are bijections because the embeddings are injective. Reordering coordinates gives a matrix A=[[B,C],[D,E]] with B=P[rows,cols]. Let T:F→R^d×R^I be the row coordinate isomorphism; the column coordinate isomorphism does not change the image of the presentation map.
2. Since det(B) is a unit, choose a with a det(B)=det(B)a=1. Put B'=a adj(B). Cofactor expansion gives B adj(B)=adj(B)B=det(B)I: diagonal entries are the determinant expansion and off-diagonal entries are determinants with repeated rows or columns. Thus BB'=B'B=I. These equalities also hold for the empty block when d=0.
3. Fix i in I and j in J. Extend the specified row list by i and the column list by j; both are injective selections of length d+1. Their minor is [[B,C_j],[D_i,E_ij]], and its determinant is zero by the hypothesis. Subtract from its last row the linear combination of its first d rows with coefficients D_i B'. This preserves the determinant: by multilinearity each added term has a repeated row and vanishes. The resulting last row is [0,E_ij-D_i B' C_j]. Expanding along this last row gives 0=det(B)(E_ij-D_i B' C_j). Multiplication by a proves E_ij=D_i B' C_j. Hence E=DB'C. If either complementary index set is empty there are no entries to prove; if d=0 the same computation says every entry of P is a vanishing 1-minor.
4. Define U=[[B',0],[-DB',I]] and V=[[I,-B'C],[0,I]]. Direct block multiplication shows that their inverses are [[B,0],[D,I]] and [[I,B'C],[0,I]], respectively, and that UAV=[[I,0],[0,0]]. Let W=U∘T. Since the column reordering and V are invertible, W sends the image of P exactly onto the first summand R^d×{0}. This follows also directly from the displayed diagonal matrix, which maps (x,y) to (x,0).
5. Define φ=π∘W⁻¹:R^d×R^I→M. It is surjective because π is, and its kernel is R^d×{0}, by the assumed equality ker π=im P and Step 4. Define ψ:R^I→M by ψ(b)=φ(0,b). Given m, choose (a,b) with φ(a,b)=m. Since φ(a,0)=0, ψ(b)=m, proving surjectivity. If ψ(b)=0, then (0,b) lies in the first summand, so b=0, proving injectivity. Therefore ψ is a linear isomorphism; its inverse is linear because ψ is linear and bijective.
6. Set s(m)=W⁻¹(0,ψ⁻¹(m)). This is R-linear and π(s(m))=φ(0,ψ⁻¹(m))=m, so π.comp s=id. All constructions and identities remain valid in the zero ring and with empty complementary sets, so the statement has no additional nontriviality or dimension assumptions.

## Key steps

1. Reorder the selected rows and columns into an initial square block.
2. Invert that block using its unit determinant and the adjugate identities.
3. Apply the vanishing hypothesis to bordered minors to prove the Schur complement is zero.
4. Use explicit invertible block operations to identify the presentation image with the first coordinate summand.
5. Identify M with the complementary coordinate module.
6. Transport the complementary inclusion back to obtain a section of π.

## Reference use

### local-project

Queries:
- `fittingIdeal|fitting_ideal|determinantal|minor.*[Pp]rojectiv|[Pp]rojectiv.*minor`
- `baseChange|Projective|split_surjective|projective`
- `det_fromBlocks|det_mul|det_submatrix|isUnit_det|adjugate`
- `def map|map_mk|map_surjective|namespace LocalizedModule`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean CheckInstances.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean HeaderPolicyCheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/Projective.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/LocalizedModule/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/LocalizedModule/Exact.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Ideal/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Localization/Module.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/LocalProperties/Projective.lean`
- `/tmp/p05-ptm-decomp-e4krhmb5/build/CheckTypes.lean`
- `/tmp/p05-ptm-decomp-e4krhmb5/build/CheckInstances.lean`
- `/tmp/p05-ptm-decomp-e4krhmb5/CheckTypes.log`
- `/tmp/p05-ptm-decomp-e4krhmb5/CheckInstances.log`
- `/tmp/p05-ptm-decomp-e4krhmb5/HeaderPolicyCheck.log`
- `/tmp/p05-ptm-decomp-e4krhmb5/header-input-binding.json`
- `/tmp/p05-ptm-decomp-e4krhmb5/name-audit.json`
- `/tmp/p05-ptm-decomp-e4krhmb5/pins.json`
- `/tmp/p05-ptm-decomp-e4krhmb5/interface-report.json`

The project and mathlib snapshots are clean at 2fdd42759f4ab17640ac773289b521dd69d4b26e and db584cd6d46c92f209a44c0f1c829460d327499d; all nine compiler dependency checkouts match their clean pins. The targeted search found no determinantal projectivity criterion. Available infrastructure includes Schur-complement determinants, localization exactness, Ideal.span_range_pow_eq_top, and Module.Projective.of_split. Both proposed literal types elaborate after import Submission. Anonymous Lean proofs verify matrix-vector multiplication, localization-ring linearity, the localized map's fraction formula, and the scalar interpretation of the unit-determinant hypothesis. Eight inspected infrastructure declarations have transitive axiom closures contained in propext, Classical.choice, and Quot.sound. Neither proposed name occurs in the ten active DAG registries or imported environment. Private compiler copies follow policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, omitting exactly lines 10–11; Lean confirms all 13 omitted targets absent. Exact omitted text and reversible original/build hashes are recorded in header-input-binding.json. Protected sources and handoffs were not edited. These checks validate decomposition interfaces; theorem acceptance still requires the configured exact-contract comparator and independent review.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/622

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
