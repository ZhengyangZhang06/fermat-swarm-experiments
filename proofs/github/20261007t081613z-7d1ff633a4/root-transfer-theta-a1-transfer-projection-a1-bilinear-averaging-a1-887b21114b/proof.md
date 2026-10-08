# Parent-supplied natural-language proof

- Parent DAG node: `root.transfer_theta-a1.transfer_projection-a1`
- Child DAG node: `root.transfer_theta-a1.transfer_projection-a1.bilinear_averaging-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix t,F,Q,x,y and an index i. Equivariance of φ rewrites the i-th summand as φ(ρA(t_i)F(t_i⁻¹·x),ρB(t_i)Q(t_i⁻¹·y)). This uses the given equivariance equality in its reverse direction and does not exchange the two arguments.
2. Suppose F is G-equivariant. Applying this equivariance at t_i and t_i⁻¹·x, and using t_i·(t_i⁻¹·x)=x, gives ρA(t_i)F(t_i⁻¹·x)=F(x). Thus each summand from step 1 equals φ(F(x),ρB(t_i)Q(t_i⁻¹·y)).
3. Sum the equalities of step 2. Linearity of b↦φ(F(x),b) moves the finite sum inside the second argument. The result is precisely the first projection identity.
4. Suppose instead Q is G-equivariant. Applying its equivariance at t_i and t_i⁻¹·y gives ρB(t_i)Q(t_i⁻¹·y)=Q(y). The summand in step 1 is therefore φ(ρA(t_i)F(t_i⁻¹·x),Q(y)).
5. Sum these equalities and use additivity in the first argument of φ, equivalently evaluate the sum of linear maps φ(ρA(t_i)F(t_i⁻¹·x)) at Q(y). This yields the second identity. Empty sums are included because both linear maps send zero to zero. All choices were arbitrary, so both conditional identities hold with exactly the stated hypotheses.

## Key steps

1. Use equivariance of φ to move the representation action onto its two inputs.
2. If F is equivariant, cancel its translated input and sum in the second argument.
3. If Q is equivariant, cancel its translated input and sum in the first argument.
4. Keep the order of the two factors throughout.

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
