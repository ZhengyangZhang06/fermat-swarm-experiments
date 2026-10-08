# Parent-supplied natural-language proof

- Parent DAG node: `root.transfer_theta-a1`
- Child DAG node: `root.transfer_theta-a1.theta_from_pairings-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix ℓ. For each i and x, define Θ_i(x) to be the functional y↦ℓ(P_i(x,y)). Linearity of P_i in its second argument and of ℓ makes this a member of the full algebraic dual. Linearity of P_i in its first argument makes x↦Θ_i(x) linear. This construction already gives the asserted evaluation formula.
2. Consider IsTheta0. Given m,z and any e satisfying its pointwise premise, the hypothesis on P₀ supplies a level cocycle e₀ with the same pointwise function and P₀(m,[z])=[e₀]. Function extensionality and subtype extensionality give e=e₀. Consequently Θ₀(m)([z])=ℓ([e₀])=ℓ([e]), as required for every e in the predicate.
3. For IsTheta1, given f,hf,g,hg and any e in its premise, the P₁ hypothesis supplies e₁ whose underlying function is precisely cupCochain φ f g. Thus e=e₁ by the same extensionality argument, and Θ₁([f])([g])=ℓ(P₁([f],[g]))=ℓ([e₁])=ℓ([e]). The continuousH1 subtype representatives are exactly those displayed in the frozen predicate; proof irrelevance identifies any membership proofs.
4. For IsTheta2, apply the P₂ hypothesis to z,d, identify its witness with the arbitrary e in the predicate by pointwise equality, and conclude Θ₂([z])(d)=ℓ([e]). Hence all three predicates hold.
5. Let Ψ satisfy the predicates. Every continuousH2 class is [z] for some level two-cocycle z, by surjectivity of the quotient map. For an invariant m and such a z, insert the supplied P₀ witness into IsTheta0 for Ψ. This gives Ψ₀(m)([z])=ℓ(P₀(m,[z]))=Θ₀(m)([z]), hence equality on every degree-zero input pair.
6. Every continuousH1 class has a level one-cocycle representative by the defining submodule-image formula. Choose such representatives for both degree-one inputs and insert the supplied P₁ witness into IsTheta1 for Ψ. It gives Ψ₁(x)(y)=ℓ(P₁(x,y))=Θ₁(x)(y) for every pair x,y.
7. Represent any degree-two first input as [z]; the second input is already invariant. Insert the P₂ witness into IsTheta2 for Ψ to obtain equality with Θ₂ on this pair. Thus equality holds on all pairs in all three degrees.
8. Extensionality of functionals and then of linear maps yields Ψ_i=Θ_i for i=0,1,2. These cases exhaust Fin 3, proving the asserted degreewise uniqueness.

## Key steps

1. Curry ℓ composed with each bilinear P_i into a map to the full dual.
2. Identify every universally quantified theta witness with the supplied actual product cocycle.
3. Use quotient surjectivity for H² and the image definition for H¹.
4. Evaluate any competing theta family on representatives and conclude by extensionality.

## Reference use

### local-project

Queries:
- `rg -n 'def (continuousH|levelCo|IsTheta)|theorem.*(theta|transfer|cores)|normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup|H1π_eq|cupCochain' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory`
- `rg -n 'transfer|corestriction|prism|normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_Continuous*.lean .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology`
- `rg -n 'splittingField|finiteDimensional|Normal' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/Normal/Basic.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousDuality.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/Normal/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/Algebra/Group/Subgroup/Basic.lean`

The snapshot pins project 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. continuousH1 is the image of level one-cocycles in ordinary H1; continuousH2 is the quotient by the pulled-back image of level one-cochains. The theta predicates universally quantify over product-cocycle witnesses, so uniqueness needs actual witnesses. CupProduct supplies the middle product formula and explicit boundary primitives; LowDegree supplies H1π_eq_zero_iff and H1π_eq_iff. Normal/Basic supplies normality of splitting fields, and Subgroup/Basic supplies normality under comap. The focused continuous/cohomology search found no transfer, corestriction, prism implementation, or either policy-listed groupCohomology instance.
