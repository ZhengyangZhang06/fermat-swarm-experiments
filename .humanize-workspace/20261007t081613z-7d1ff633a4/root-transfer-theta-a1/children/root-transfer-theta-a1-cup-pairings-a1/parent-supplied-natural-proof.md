# Parent-supplied natural-language proof

- Parent DAG node: `root.transfer_theta-a1`
- Child DAG node: `root.transfer_theta-a1.cup_pairings-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write d₀v(s)=s·v−v, d₁f(s,t)=s·f(t)−f(st)+f(s), and d₂z(s,t,u)=s·z(t,u)−z(st,u)+z(s,tu)−z(s,t), exactly the pinned differentials. Define the three proposed cocycle functions by e₀(s,t)=φ(m,z(s,t)), e₁(s,t)=φ(f(s),s·g(t)), and e₂(s,t)=φ(z(s,t),d).
2. If m is invariant, the linear map b↦φ(m,b) is equivariant, since s·φ(m,b)=φ(s·m,s·b)=φ(m,s·b). Therefore it commutes with d₁ and d₂, and e₀ is a two-cocycle. Likewise a↦φ(a,d) is equivariant when d is invariant, so e₂ is a two-cocycle. Their level conditions follow by postcomposition from the level condition of z.
3. For e₁, expand d₂e₁. Equivariance changes its first term into φ(s·f(t),st·g(u)). The one-cocycle identities f(st)=s·f(t)+f(s) and g(tu)=t·g(u)+g(t) give the full sum φ(s·f(t),st·g(u))−φ(s·f(t)+f(s),st·g(u))+φ(f(s),st·g(u)+s·g(t))−φ(f(s),s·g(t)), which is zero by bilinearity.
4. Choose finite witness fields F_f and F_g for f and g and take F=E₀⊔F_f⊔F_g. This compositum is finite-dimensional over ℚ. If r(k) and r(l) fix F, then f(sk)=f(s), g(tl)=g(t), and k acts trivially on B. Thus e₁(sk,tl)=φ(f(s),s·(k·g(t)))=e₁(s,t). This makes e₁ an actual level two-cocycle. All three constructions are bilinear before taking classes; addition and scalar multiplication can be checked pointwise, using a common finite compositum for levels.
5. For the (0,2) product, changing z by d₁u for a level one-cochain u changes e₀ by d₁(t↦φ(m,u(t))). The primitive is level by postcomposition. For the (2,0) product the corresponding primitive is t↦φ(u(t),d). Hence both endpoint products annihilate the exact denominator defining continuousH2, namely level coboundaries pulled back to level cocycles. Their bilinear maps therefore descend to the required H² inputs.
6. For the (1,1) product, if f=d₀a, let v(t)=φ(a,g(t)). The one-cocycle identity for g and equivariance give d₁v(s,t)=φ(s·a−a,s·g(t))=e₁(s,t). This primitive is level because g is level. If instead g=d₀b and f is a one-cocycle, put u(s)=φ(f(s),s·b). Direct expansion using f(st)=s·f(t)+f(s) gives d₁u(s,t)=−φ(f(s),s·(t·b−b))=−e₁(s,t). Refine the level of f with E₀. For k fixing that refinement, u(sk)=φ(f(s),s·(k·b))=u(s), so −u is a level primitive for e₁.
7. By the pinned H1π_eq_iff, equal ordinary H¹ classes of one-cocycles differ by d₀a for some a. Therefore Step 6 makes the product independent of either level representative of a continuousH1 class. Changing both representatives is handled successively. Every continuousH1 class has such a representative by its defining image formula. Bilinearity on representatives consequently gives a bilinear map on the two frozen continuousH1 carriers.
8. Use these descended maps as P₀,P₁,P₂, and curry each bilinear map into the displayed linear-map type. For each requested representative tuple, use the actual level two-cocycle constructed in Steps 1–4. The quotient construction and the descent in Steps 5–7 give exactly the three asserted class equalities. Indexing the three maps by Fin 3 only packages these already constructed maps.

## Key steps

1. Construct the three pointwise product functions and verify their two-cocycle equations.
2. Obtain actual level witnesses; the middle product uses a common field fixing B.
3. For the endpoint products, send level boundary primitives through equivariant linear maps.
4. For the middle product, use explicit level primitives for a boundary in either factor.
5. Use H1π_eq_iff and the continuousH2 quotient to descend bilinearly.
6. Return the three bilinear maps together with all representative witnesses.

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
