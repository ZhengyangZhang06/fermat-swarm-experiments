# Parent-supplied natural-language proof

- Parent DAG node: `root.transfer_theta-a1.transfer_projection-a1`
- Child DAG node: `root.transfer_theta-a1.transfer_projection-a1.low_degree_prism-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. For the first assertion fix a two-variable F satisfying the stated cocycle equation and x,y∈X. Applying that equation to (αx,βx,βy) gives F(βx,βy)−F(αx,βy)+F(αx,βx)=0. Applying it to (αx,αy,βy) gives F(αy,βy)−F(αx,βy)+F(αx,αy)=0.
2. Subtract the second equality from the first. The two occurrences of F(αx,βy) cancel. Rearranging in the abelian group V gives F(βx,βy)−F(αx,αy)=F(αy,βy)−F(αx,βx), as required.
3. For the second assertion fix a three-variable F satisfying its stated cocycle equation and x,y,z∈X, and define h as in the statement. Apply the cocycle equation to the three quadruples (αx,βx,βy,βz), (αx,αy,βy,βz), and (αx,αy,αz,βz). The resulting zero expressions are respectively E₀=F(βx,βy,βz)−F(αx,βy,βz)+F(αx,βx,βz)−F(αx,βx,βy), E₁=F(αy,βy,βz)−F(αx,βy,βz)+F(αx,αy,βz)−F(αx,αy,βy), and E₂=F(αy,αz,βz)−F(αx,αz,βz)+F(αx,αy,βz)−F(αx,αy,αz).
4. Form E₀−E₁+E₂=0. The terms F(αx,βy,βz) and F(αx,αy,βz) each cancel with their opposite. The remaining expression is F(βx,βy,βz)−F(αx,αy,αz)−h(y,z)+h(x,z)−h(x,y)=0. Rearranging proves the second identity.
5. The arguments apply to every F and all indicated vertices, proving both universally quantified assertions for the given α and β.

## Key steps

1. Evaluate the degree-one cocycle identity on the two triangles of a prism.
2. Subtract and cancel to obtain the degree-one coboundary formula.
3. Evaluate the degree-two cocycle identity on the three tetrahedra of a prism.
4. Take their alternating sum, cancel internal faces, and identify the explicit h.

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
