<!-- theorem-id: fermat-p02/root.primitive_parabolic-a1.integral_parabolic_normal_form-a1.primitive_eigenvector_triangular-a1 -->

## Theorem `Submission.p02_es_177ebb5a_pnf_primitive_eigenvector_triangular`

Let γ∈SL₂(ℤ) and ε,p,q∈ℤ. Assume ε²=1, IsCoprime p q, and γ(p,q)ᵀ=(εp,εq)ᵀ. Then there exist σ∈SL₂(ℤ) and b∈ℤ such that the underlying matrix of σ⁻¹γσ is (ε b;0 ε).

Node: `root.primitive_parabolic-a1.integral_parabolic_normal_form-a1.primitive_eigenvector_triangular-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/2

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/72

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p02_es_177ebb5a_pnf_primitive_eigenvector_triangular`

```lean
∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε p q : ℤ), ε ^ 2 = 1 → IsCoprime p q → (γ : Matrix (Fin 2) (Fin 2) ℤ).mulVec ![p, q] = ![ε * p, ε * q] → ∃ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (b : ℤ), (σ⁻¹ * γ * σ : Matrix.SpecialLinearGroup (Fin 2) ℤ).val = Matrix.of ![![ε, b], ![0, ε]]
```

### Frozen project context

`Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean` at `1f74c284b125d4c45f527f2d621597fcf1e103a9` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HeckeEis_eichlerShimuraMap_injective.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_injective (N : ℕ) [NeZero N] (n : ℕ) :
    Function.Injective
      (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f) := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_parabolic-a1.integral_parabolic_normal_form-a1`
- Child DAG node: `root.primitive_parabolic-a1.integral_parabolic_normal_form-a1.primitive_eigenvector_triangular-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix γ∈SL₂(ℤ) and ε,p,q∈ℤ with ε²=1, IsCoprime p q, and γ(p,q)=ε(p,q). By the definition of IsCoprime, choose u,v∈ℤ satisfying up+vq=1.
2. Put r=−v and s=u, and let S=(p r;q s). Its determinant is ps−qr=pu+qv=up+vq=1. Thus S defines an element σ∈SL₂(ℤ), whose inverse has integral entries because it is the adjugate of S.
3. Let δ=σ⁻¹γσ and let e₁=(1,0). Since σe₁=(p,q), the eigenvector hypothesis and associativity of matrix-vector multiplication give δe₁=σ⁻¹γ(p,q)=σ⁻¹(ε(p,q))=εσ⁻¹σe₁=εe₁. Thus the first column of δ is (ε,0).
4. Set b=δ₁₂ and d=δ₂₂, so the underlying integral matrix of δ is (ε b;0 d). As δ∈SL₂(ℤ), its determinant is one. The 2×2 determinant formula therefore gives εd=1.
5. Multiply εd=1 by ε. Since ε²=1, this yields d=ε. Consequently δ=(ε b;0 ε), exactly the matrix represented by Matrix.of ![![ε,b],![0,ε]]. The σ and b already constructed are the required witnesses.

## Key steps

1. Extract Bézout coefficients from IsCoprime p q.
2. Complete (p,q) to the first column of a determinant-one integral matrix.
3. Transport the eigenvector equation through conjugation to determine the first column.
4. Use determinant one and ε²=1 to determine the second diagonal entry.
5. Return the constructed conjugating matrix and upper-right entry.

## Reference use

### local-project

Queries:
- `parabolic|trace.*(4|2)|trace_sq|IsCoprime|gcdA|zpow.*T|eichlerShimuraMap_injective`
- `parabolic.*conjug|conjug.*parabolic|trace.*(sq|\^ 2)|primitive.*(ker|eigen)|exists.*(ker|coprime)`
- `coe_T_zpow|T_zpow|def T|theorem coe_mul|theorem coe_neg|mkOf`
- `det_fin_two|mulVec_fin_two|mulVec_smul|mulVec_mulVec|def IsCoprime`
- `p02_es_177ebb5a_pnf_(primitive_kernel|primitive_eigenvector_triangular)`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_177ebb5a_pnf_decomposition.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Int/GCD.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/Coprime/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/Coprime/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/Submission.lean`
- `/tmp/p02_177ebb5a_pnf_decomposition.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib has that revision and clean Git status; the five compared supporting mathlib files and Def_Gamma0CoeffCohomology.lean match the snapshot byte-for-byte. The snapshot supplies Int.gcd_eq_gcd_ab, Int.exists_gcd_one, Int.isCoprime_iff_gcd_eq_one, Matrix.det_fin_two, matrix-vector identities, and ModularGroup.coe_T_zpow. No matching integral conjugacy theorem was found in the searched project and matrix/modular-form sources. Both proposed names have no matches in Submission or the current DAG metadata. Both exact child types elaborate after import Submission. Additional checked examples verify special-linear multiplication and negation, the constructed matrix determinant, and matrix-vector multiplication. Transitive axiom checks on eleven supporting declarations report only propext, Classical.choice, and Quot.sound. These establish interface compatibility and reference suitability, not comparator acceptance of new proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/169

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
