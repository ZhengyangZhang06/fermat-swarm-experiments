<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1 -->

## Theorem `Submission.f036cc6b1f_pic_mec_pointwise_sign_partition`

Let G = SL₂(ℤ) act canonically on the upper half-plane ℍ with its Borel measurable structure. Let Δ ≤ G contain −I, and let E,F,X ⊆ ℍ be measurable. Assume γz ∈ X if and only if z ∈ X for every γ ∈ Δ and z ∈ ℍ. Assume also that, for each S equal to E or F and every z ∈ X, there exists r ∈ Δ such that rz ∈ S and every δ ∈ Δ with δz ∈ S satisfies δ = r or δ = −r. Then there exist families A,B : Δ → Set ℍ whose members are measurable, such that each family is pairwise disjoint, ⋃γ Aγ = E ∩ X, ⋃γ Bγ = F ∩ X, and the image of Aγ under z ↦ γ⁻¹z is exactly Bγ for every γ ∈ Δ.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/211

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/221, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/222

## Lean problem

Declaration: `Submission.f036cc6b1f_pic_mec_pointwise_sign_partition`

```lean
∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F X : Set UpperHalfPlane), (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → MeasurableSet E → MeasurableSet F → MeasurableSet X → (∀ (γ : Δ) (z : UpperHalfPlane), (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X) → (∀ S : Set UpperHalfPlane, (S = E ∨ S = F) → ∀ z ∈ X, ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ S ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ) → ∃ A B : Δ → Set UpperHalfPlane, (∀ γ, MeasurableSet (A γ)) ∧ (∀ γ, MeasurableSet (B γ)) ∧ Pairwise (fun γ δ => Disjoint (A γ) (A δ)) ∧ Pairwise (fun γ δ => Disjoint (B γ) (B δ)) ∧ (⋃ γ, A γ) = E ∩ X ∧ (⋃ γ, B γ) = F ∩ X ∧ (∀ γ : Δ, (fun z : UpperHalfPlane => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z) '' (A γ) = B γ)
```

### Frozen project context

`Fermat/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean` at `61b5f85556ac71631ccad822e0694511234f7132` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data and hypotheses. For g ∈ G write T_g(z) = gz. The canonical action agrees with the action of Matrix.SpecialLinearGroup.mapGL ℝ g. The pinned UpperHalfPlane.instContinuousGLSMul therefore shows that T_g is continuous and measurable. Its inverse is T_{g⁻¹}, by the group action laws. ModularGroup.SL_neg_smul gives T_{−g} = T_g.
2. Negation preserves Δ: if g ∈ Δ, then −g = (−I)g ∈ Δ because −I ∈ Δ. Matrix multiplication gives (−I)g = g(−I) = −g and (−I)² = I. Thus −I is central and is its own inverse. It follows that (−g)⁻¹ = g⁻¹(−I) = −g⁻¹. Also −(−g) = g.
3. On Δ define p ∼ q to mean that their underlying matrices satisfy q = p or q = −p. This is an equivalence relation. Reflexivity follows from equality. For symmetry, q = p gives p = q, while q = −p gives p = −q by negating both sides. For transitivity, write q = p or −p and r = q or −q; substitution gives r = p or −p in all four cases, using double negation. Choose one representative from each equivalence class, and let L ⊆ Δ be the set of chosen representatives. Each class is nonempty, so this choice is available. Every p ∈ Δ equals γ or −γ for some γ ∈ L. If γ,η ∈ L differ only by sign, they belong to the same equivalence class and therefore are the same chosen representative. Symmetry also gives γ = p or γ = −p when γ represents the class of p.
4. We record a consequence of the pointwise representative hypothesis. Fix S equal to E or F, z ∈ X, and p,q ∈ Δ with pz,qz ∈ S. Choose the stipulated witness r. Both p and q equal r or −r. If both equal r, or both equal −r, then q = p. If p = r and q = −r, then q = −p. If p = −r and q = r, double negation again gives q = −p. Hence q = p or q = −p.
5. Define families indexed by every γ ∈ Δ. If γ ∈ L, set Aγ = E ∩ X ∩ {z : γ⁻¹z ∈ F} and Bγ = F ∩ X ∩ {z : γz ∈ E}. If γ ∉ L, set Aγ = Bγ = ∅. Here all actions use the underlying matrices of the subgroup elements. The first preimage condition is equivalent to z ∈ γF, and the second to z ∈ γ⁻¹E, because the action maps are inverse bijections.
6. For γ ∈ L, the final factors defining Aγ and Bγ are measurable preimages of F and E under T_{γ⁻¹} and T_γ, respectively. Intersecting them with the measurable sets E,F,X preserves measurability. For γ ∉ L, both pieces are empty and measurable. Thus every member of both families is measurable.
7. Every Aγ is contained in E ∩ X. Conversely, take z ∈ E ∩ X. The hypothesis for F supplies δ ∈ Δ with δz ∈ F. Choose γ ∈ L representing δ⁻¹. Then γ = δ⁻¹ or γ = −δ⁻¹. By step 2, γ⁻¹ = δ or γ⁻¹ = −δ. Sign invariance of the action gives γ⁻¹z = δz ∈ F in either case. Therefore z ∈ Aγ. These two inclusions prove ⋃γ Aγ = E ∩ X.
8. Every Bγ is contained in F ∩ X. Conversely, take z ∈ F ∩ X. The hypothesis for E supplies δ ∈ Δ with δz ∈ E. Choose γ ∈ L representing δ, so γ = δ or γ = −δ. Sign invariance gives γz = δz ∈ E. Therefore z ∈ Bγ, proving ⋃γ Bγ = F ∩ X.
9. To prove pairwise disjointness of the A-family, suppose z belongs to both Aγ and Aη. Neither piece is empty, so γ,η ∈ L. Moreover z ∈ X and γ⁻¹z,η⁻¹z ∈ F. Since γ⁻¹,η⁻¹ ∈ Δ, step 4 gives η⁻¹ = γ⁻¹ or η⁻¹ = −γ⁻¹. Taking inverses and using step 2 yields η = γ or η = −γ. The defining property of L then gives η = γ, including equality as subgroup elements because their underlying matrices are equal. Thus distinct indices cannot have intersecting A-pieces, which is the required pairwise disjointness.
10. Suppose z belongs to both Bγ and Bη. Then γ,η ∈ L, z ∈ X, and γz,ηz ∈ E. Step 4 gives η = γ or η = −γ, and the representative property of L gives η = γ. Hence the B-family is also pairwise disjoint.
11. Fix γ ∈ L. If z ∈ Aγ and y = γ⁻¹z, then y ∈ F by the definition of Aγ. Invariance of X under γ⁻¹ gives y ∈ X. The group action law gives γy = z ∈ E, so y ∈ Bγ. This proves T_{γ⁻¹}(Aγ) ⊆ Bγ. Conversely, if y ∈ Bγ, put z = γy. Then z ∈ E by the definition of Bγ and z ∈ X by invariance. Also γ⁻¹z = y ∈ F, so z ∈ Aγ and y = T_{γ⁻¹}(z). This proves the reverse inclusion. Consequently T_{γ⁻¹}(Aγ) = Bγ.
12. If γ ∉ L, both pieces are empty and their required image equality holds because the image of the empty set is empty. Combining this with step 11, the measurability from step 6, the exact union identities from steps 7 and 8, and the disjointness from steps 9 and 10 proves the full conclusion.

## Key steps

1. Establish measurability of the canonical action maps and invariance of the action under matrix negation.
2. Show that negation preserves Δ and that inversion commutes with negation.
3. Choose exactly one representative of every sign-equivalence class in Δ.
4. Derive pairwise uniqueness modulo sign from each pointwise representative hypothesis.
5. Define the matched pieces by measurable action preimages, setting unselected indices to empty.
6. Prove the exact covering identities using representatives of δ⁻¹ for A and δ for B.
7. Prove disjointness using uniqueness modulo sign and uniqueness of the selected representatives.
8. Use invariance of X and inverse action identities to prove the exact image correspondence.

## Reference use

### local-project

Queries:
- `SL_neg_smul|measurePreserving.*(smul|SMul)|span_heckeTLin_eigen_eq_top|measurable.*(fundamental|Fundamental)|IsFundamentalDomain`
- `measurePreserving|continuous.*smul|mapGL|volume`
- `invariant.*conull|conull.*invariant|equidecomposition|unique.*sign`
- `neg_inv|inv_neg|hasDistribNeg|DistribNeg|Neg.*SL|instNeg|neg_neg`
- `f036cc6b1f_pic_mec_invariant_conull_core|f036cc6b1f_pic_mec_pointwise_sign_partition`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false /tmp/fermat-p01-mec-decomposition-check/Check.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/Action.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/FundamentalDomain.lean`
- `/tmp/fermat-p01-mec-decomposition-check/Check.lean`
- `/tmp/fermat-p01-mec-decomposition-check/Check-configured.log`
- `/tmp/fermat-p01-mec-decomposition-check/types.json`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Measure.lean defines hyperbolic volume and proves GL₂(ℝ)-invariance; Topology.lean supplies continuous action maps; MoebiusAction.lean identifies the SL action through mapGL and supplies ModularGroup.SL_neg_smul. SpecialLinearGroup.lean supplies matrix negation and HasDistribNeg. FundamentalDomain.lean requires disjointness of group translates, so its domain results cannot be applied directly to Δ when −I acts trivially. The targeted project/Definitions search found no relevant invariant-conull-core or sign-equidecomposition declaration. Both proposed identifiers were absent from the searched DAG and node artifacts. Both final types elaborate after literal import Submission, with exit code 0. Instance inspection confirmed UpperHalfPlane.instMeasureSpace and UpperHalfPlane.SLAction; an anonymous check established countability explicitly. The audited action, continuity, volume, and measure-invariance declarations use only propext, Classical.choice, and Quot.sound as transitive axioms. All nine dependency repositories were clean at their pinned revisions, and all twenty rebuilt local import sources matched the snapshot. These are interface and infrastructure checks, not comparator acceptance of the proposed child proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/489

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
