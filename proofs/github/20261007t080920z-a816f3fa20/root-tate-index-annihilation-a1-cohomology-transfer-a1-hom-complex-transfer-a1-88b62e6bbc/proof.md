# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1`
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data. Write U^m = Hom_G(X_m,A) and V^m = Hom_H(Res_H X_m,Res_H A). These are k-modules, and their differentials send F to F ∘ ∂_(m+1). They are exactly the two linearYonedaObj complexes in the statement. Let d = H.index.
2. Choose a left transversal T, one representative t for each left coset tH. Since G is finite, T is finite. The assignment t ↦ tH is a bijection from T to G/H, so |T| = d by the definition of subgroup index as the cardinality of G/H.
3. Define R_m : U^m → V^m by retaining the same underlying k-linear map and forgetting part of its equivariance. For F ∈ V^m define (C_m F)(x) = Σ_{t∈T} ρ_A(t)(F(ρ_(X_m)(t⁻¹)(x))). Each summand is k-linear in x, because all three maps being composed are k-linear. The expression is also k-linear in F, since composition with fixed linear maps and finite summation preserve addition and scalar multiplication.
4. For t ∈ G and h ∈ H, the summand indexed by th equals that indexed by t. Indeed, ρ_A(th)F(ρ_(X_m)((th)⁻¹)x) = ρ_A(t)ρ_A(h)F(ρ_(X_m)(h⁻¹)ρ_(X_m)(t⁻¹)x) = ρ_A(t)F(ρ_(X_m)(t⁻¹)x), using H-equivariance of F and cancellation of the actions of h and h⁻¹. Any two representatives of the same left coset differ by right multiplication by an element of H. Matching representatives by their cosets therefore proves that the finite sum defining C_m is independent of the chosen transversal.
5. Fix g ∈ G. Left multiplication permutes left cosets, and gT is another left transversal. Evaluate C_m F at ρ_(X_m)(g)x using gT. The summand indexed by gt is ρ_A(gt)F(ρ_(X_m)((gt)⁻¹)ρ_(X_m)(g)x) = ρ_A(g)ρ_A(t)F(ρ_(X_m)(t⁻¹)x). Summing and using linearity of ρ_A(g) gives (C_m F)(ρ_(X_m)(g)x) = ρ_A(g)((C_m F)(x)). Hence C_m F is G-equivariant. Together with step 3, this proves that C_m is a well-defined k-linear map V^m → U^m; R_m is k-linear as well.
6. Every differential ∂_(m+1) of X is G-equivariant. Thus ρ_(X_m)(t⁻¹) ∘ ∂_(m+1) = ∂_(m+1) ∘ ρ_(X_(m+1))(t⁻¹). Substituting this into the defining finite sum gives (C_m F) ∘ ∂_(m+1) = C_(m+1)(F ∘ ∂_(m+1)). Restriction plainly satisfies the same differential compatibility because it retains the underlying map. These identities, and the automatic identities for zero differentials outside adjacent degrees, assemble the R_m and C_m into cochain maps R and C.
7. If F ∈ U^m, its G-equivariance gives F(ρ_(X_m)(t⁻¹)x) = ρ_A(t⁻¹)F(x). Consequently every summand of C_m(R_m F)(x) is ρ_A(t)ρ_A(t⁻¹)F(x) = F(x). There are exactly d summands, so C_m(R_m F)(x) = d • F(x), with • denoting repeated addition.
8. Equality for every x proves C_m(R_m F) = d • F as equivariant linear maps. Equality for every F proves C_m ∘ R_m = d • id_(U^m). Natural-number multiplication on cochain morphisms is degreewise repeated addition, so equality in every degree proves C ∘ R = d • id_U. The maps from step 6 are the required witnesses.

## Key steps

1. Identify both cochain complexes as equivariant Hom modules with precomposition differentials.
2. Choose a finite left transversal and identify its cardinality with the subgroup index.
3. Define restriction and coset averaging, checking linearity.
4. Prove representative independence and use the translated transversal to establish G-equivariance.
5. Use equivariance of the chain differential to obtain cochain maps.
6. Evaluate averaging on G-equivariant maps and conclude the degreewise index identity.

## Reference use

### local-project

Queries:
- `rg -n 'transfer|cores' mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/Shapiro.lean`
- `rg -n 'linearYonedaObj' mathlib/Mathlib/Algebra mathlib/Mathlib/CategoryTheory -g '*.lean' | head -45`
- `rg -n 'def resFunctor|abbrev resFunctor|def res |abbrev res ' mathlib/Mathlib -g '*.lean' | head -35`
- `rg -n 'homologyIso|homologyMap_eq' mathlib/Mathlib/Algebra/Homology/Homotopy.lean`
- `rg -n 'index.*card|card.*index' mathlib/Mathlib/GroupTheory/Index.lean mathlib/Mathlib/GroupTheory/Coset/Card.lean | head -35`
- `rg -n 'hasNatScalar|nsmul|AddCommGroup' mathlib/Mathlib/Algebra/Homology/Additive.lean | head -35`
- `rg -n 'p04_tia_coh_restricted_standard_homotopy_equiv|p04_tia_coh_hom_complex_transfer' project mathlib/Mathlib -g '*.lean'`
- `sed -n '160,230p' mathlib/Mathlib/RepresentationTheory/Homological/Resolution.lean`
- `sed -n '317,448p' mathlib/Mathlib/RepresentationTheory/Homological/Resolution.lean`
- `sed -n '35,101p' mathlib/Mathlib/Algebra/Homology/Additive.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions/Def_GroupCohomology_TateCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/Resolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/Shapiro.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/CategoryTheory/Abelian/Ext.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/Homology/Homotopy.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/Homology/Additive.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Index.lean`

The manifest pins project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected installed sources match the snapshot; all nine installed dependencies match their pins and have clean source trees. Resolution.lean supplies the homogeneous standard complex, its alternating-deletion differential, and standardResolution. Basic.lean supplies groupCohomologyIso, so the homogeneous-to-inhomogeneous comparison needs no new child. Ext.lean defines the contravariant Hom complex; Res.lean supplies linear restriction. The transfer/cores search in Basic.lean and Shapiro.lean returned no matches. Proposed names occur neither in the searched sources nor in the inspected active DAG. Both final propositions elaborate against Mathlib and the unchanged Tate definition import. Instance inspection identifies HomologicalComplex.hasNatScalar, whose definition and nsmul_f_apply confirm degreewise repeated addition. Transitive axiom checks on the standard-resolution differential, standardResolution, groupCohomologyIso, homotopy transport, and index cardinality returned only propext, Classical.choice, and Quot.sound. However, the mandatory import Submission gate remains blocked: unchanged Submission.lean:10 references the absent Representation.TateResCor.cosetDecomp_apply. Evidence is under /tmp/p04-coh-split-b6m271g9. No source repair or comparator acceptance is claimed.
