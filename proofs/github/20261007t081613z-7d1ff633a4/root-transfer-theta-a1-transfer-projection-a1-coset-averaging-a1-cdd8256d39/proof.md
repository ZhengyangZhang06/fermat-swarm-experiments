# Parent-supplied natural-language proof

- Parent DAG node: `root.transfer_theta-a1.transfer_projection-a1`
- Child DAG node: `root.transfer_theta-a1.transfer_projection-a1.coset_averaging-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define T by the finite sum in the statement. For functions F,F′ and a scalar b∈k, linearity of each ρV(t(c)) gives T(F+F′)(x)=TF(x)+TF′(x) and T(b·F)(x)=b·TF(x), by distributing finite sums. Function extensionality supplies these identities as functions, so T is a k-linear map with the required evaluation formula.
2. Let F be H-equivariant. If two representatives differ by right multiplication, say u=t h with h∈H, then u⁻¹·x=h⁻¹·(t⁻¹·x). H-equivariance gives F(u⁻¹·x)=ρV(h⁻¹)F(t⁻¹·x). Consequently ρV(u)F(u⁻¹·x)=ρV(t)ρV(h)ρV(h⁻¹)F(t⁻¹·x)=ρV(t)F(t⁻¹·x). This proves that an individual summand depends only on its left coset.
3. Fix s∈G. Left multiplication c↦sc is a permutation of G/H, with inverse c↦s⁻¹c. The elements t(sc) and s t(c) represent the same left coset, so t(sc)=s t(c)h_c for some h_c∈H. Reindex the sum for TF(s·x) using this permutation. Its c-th summand becomes ρV(s t(c)h_c)F(h_c⁻¹ t(c)⁻¹·x)=ρV(s)ρV(t(c))F(t(c)⁻¹·x), using H-equivariance exactly as in step 2. Pulling the linear map ρV(s) through the finite sum yields TF(s·x)=ρV(s)TF(x). Thus TF is G-equivariant.
4. If F is G-equivariant, apply its equivariance with t(c) and t(c)⁻¹·x. The action law gives ρV(t(c))F(t(c)⁻¹·x)=F(x). Therefore TF(x) is the sum of card(G/H) copies of F(x). By the definition of subgroup index, card(G/H)=[G:H]; in a k-module this repeated sum is ([G:H]:k)·F(x).
5. Finally, let u be any other section. For each c, the equality t(c)H=u(c)H gives h_c∈H with u(c)=t(c)h_c. Step 2 identifies the two summands for any H-equivariant F. Summing those equalities gives TF(x)=Σ_c ρV(u(c))F(u(c)⁻¹·x) for every x, proving independence of representatives for the same T.

## Key steps

1. Define T by the finite sum and prove k-linearity pointwise.
2. Use H-equivariance to cancel a change of representative t↦th.
3. Reindex left cosets by multiplication by s and obtain G-equivariance.
4. For G-equivariant F each summand equals F, giving multiplication by H.index.
5. Compare arbitrary sections term by term to prove representative independence.

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
