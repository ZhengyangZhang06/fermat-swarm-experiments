# Parent-supplied natural-language proof

- Parent DAG node: `root.transfer_theta-a1.transfer_projection-a1`
- Child DAG node: `root.transfer_theta-a1.transfer_projection-a1.normal_level_retraction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Choose one representative t_C in each right coset C=Hg, choosing t_H=1 for the coset H itself. Each coset is nonempty, so these choices exist. Every g has a unique expression g=h t_C with h∈H and C=Hg: existence follows from g∈Ht_C, and uniqueness follows by right cancellation of t_C. Define a(g)=h, as an element of H.
2. If g=h∈H, its chosen representative is 1, so a(h)=h.
3. For h₁∈H and g=a(g)t_C, the right cosets Hh₁g and Hg agree. Thus h₁g=(h₁a(g))t_C uses the same representative, and uniqueness gives a(h₁g)=h₁a(g).
4. Now fix any normal K≤G with K≤H, any g=a(g)t_C, and u∈K. Normality gives v=t_C u t_C⁻¹∈K, hence v∈H. Therefore gu=a(g)v t_C belongs to the same right coset C and its unique H-component is a(g)v. It follows that a(gu)=a(g)v and a(g)⁻¹a(gu)=v∈K.
5. The initial choice of representatives did not involve K, so this last assertion holds for every such K for the same a. The three required properties follow.

## Key steps

1. Choose right-coset representatives, with 1 representing H, and define a(g) by g=a(g)t.
2. Right cancellation gives uniqueness, the retraction property, and H-equivariance.
3. For u∈K normal in G, rewrite gu=a(g)(tut⁻¹)t.
4. Use K≤H and uniqueness to obtain a(g)⁻¹a(gu)=tut⁻¹∈K simultaneously for every normal level.

## Reference use

### local-project

Queries:
- `levelCochains|levelCocycles|levelCoboundaries|continuousH[12]|H1π_eq|cores|transfer|homogeneous`
- `transfer|corestriction|prism|normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup`
- `representative|leftCoset|rightCoset|quotientEquiv|QuotientGroup.mk|exists.*rep|out_eq`
- `index_eq_card|index_eq|def index|card_quotient|FiniteIndex`
- `H1π_eq_zero_iff|H1π_eq_iff|d₀₁_hom_apply|d₁₂_hom_apply|d₂₃_hom_apply`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/GroupTheory/Coset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/GroupTheory/Index.lean`

The snapshot pins project 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. ContinuousH1 defines the carrier as an image of level cocycles; ContinuousH2 uses the quotient by the pulled-back image of level one-cochains. LowDegree supplies the exact H1 representative kernel and equality criteria. Coset/Defs and Coset/Basic supply representative and coset-equality interfaces without requiring H.Normal; Index identifies H.index with Nat.card (G ⧸ H). The focused search of the continuous-cohomology files and mathlib group-cohomology subtree found no transfer, corestriction, prism implementation, or either policy-listed instance.
