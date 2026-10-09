# Parent-supplied natural-language proof

- Parent DAG node: `root.transfer_theta-a1.cup_pairings-a1`
- Child DAG node: `root.transfer_theta-a1.cup_pairings-a1.cup_zero_two-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. For a representation V, write d₁u(s,t)=s·u(t)−u(st)+u(s) and d₂z(s,t,u)=s·z(t,u)−z(st,u)+z(s,tu)−z(s,t). Write Z²lev(V)=levelCocycles₂ r V and D(V)=(levelCoboundaries₂ r V).comap (levelCocycles₂ r V).subtype. By definition, H²(V)=Z²lev(V)/D(V), with quotient map πV=continuousH2π r V. An element z of Z²lev(V) belongs to D(V) exactly when its underlying function equals d₁u for a level one-cochain u.
2. Fix m∈Aᴳ. The linear map Lm:B→N given by Lm(b)=φ(m,b) is equivariant: s·Lm(b)=φ(s·m,s·b)=φ(m,s·b)=Lm(s·b). Thus applying linearity to the displayed differential formulas gives d₁(Lm∘u)=Lm∘d₁u and d₂(Lm∘z)=Lm∘d₂z. In particular e(m,z)(s,t)=φ(m,z(s,t)) is a two-cocycle whenever z is.
3. If F is a finite-dimensional intermediate field witnessing the level condition of z, and r(h),r(l) fix F, then e(m,z)(sh,tl)=φ(m,z(sh,tl))=φ(m,z(s,t))=e(m,z)(s,t). Hence e(m,z) belongs to Z²lev(N). The same argument in one variable shows that Lm∘u is level whenever u is level.
4. Let z∈D(B), and choose a level u with z=d₁u. Step 2 gives e(m,z)=d₁(Lm∘u), whose primitive is level by Step 3. Therefore e(m,z) belongs to D(N) and πN(e(m,z))=0. More generally, if πB(z)=πB(z′), then z−z′∈D(B); linearity and this conclusion give πN(e(m,z))=πN(e(m,z′)).
5. Every element y of H²(B) has a representative z. Define P(m,y)=πN(e(m,z)); Step 4 proves independence of that representative. Pointwise bilinearity gives e(m+m′,z)=e(m,z)+e(m′,z), e(c·m,z)=c·e(m,z), e(m,z+z′)=e(m,z)+e(m,z′), and e(m,c·z)=c·e(m,z). These are identities of level cocycles: invariants are a submodule; sums of level functions use the finite compositum of their witness fields; scalar multiples keep the same witness. Applying πN and using the linearity and surjectivity of πB proves all four bilinearity identities for P on Aᴳ×H²(B). Curry P to obtain the asserted linear-map type.
6. For each specified m and z, use the actual level cocycle e(m,z) from Steps 2–3. Its underlying function is the required pointwise product, and the definition of P gives P(m,πB(z))=πN(e(m,z)). This proves the full representative assertion without any finite-index, normality, or trivial-action hypothesis.

## Key steps

1. For invariant m, show that b↦φ(m,b) is equivariant and commutes with both relevant differentials.
2. Postcompose a level two-cocycle to obtain an actual level two-cocycle with the same finite witness.
3. Send each level boundary primitive through that equivariant linear map, annihilating the exact continuous H² denominator.
4. Define the pairing on quotient classes and prove its four bilinearity identities from representatives.
5. Return the constructed level cocycle and its defining quotient equality.

## Reference use

### local-project

Queries:
- `rg -n 'continuous.*[Cc]up|[Cc]up.*continuous|normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory`
- `rg -n 'H1π_eq_iff|d₁₂_hom_apply|mem_cocycles₂_iff|d₂₃_hom_apply' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `rg -n 'finiteDimensional.*[Ss]up|[Ss]up.*finiteDimensional' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/IntermediateField`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2Map.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`

The manifest pins project 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. continuousH1 is the image of level one-cocycles under ordinary H1π; continuousH2 is the quotient of level two-cocycles by the pulled-back image of level one-cochains. ContinuousH2Map supplies equivariant postcomposition and preservation of this exact denominator. CupProduct supplies the ordinary cup cocycle and the two boundary-primitive calculations, but the focused search found no continuous cup-pairing descent. H1π_eq_iff identifies equal H¹ classes by coboundary differences; finiteDimensional_sup supplies the common finite levels. The focused search also found neither policy-listed instance. The four project definition files match the snapshot byte-for-byte; the local mathlib checkout is clean at the pinned revision. Diagnostic Lean axiom checks of continuousH2Map, H1π_eq_iff, cup, and continuousH2π_eq_zero_iff found only propext, Classical.choice, and Quot.sound.
