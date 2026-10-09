# Parent-supplied natural-language proof

- Parent DAG node: `root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1`
- Child DAG node: `root.transfer_theta-a1.cup_pairings-a1.cup_one_one-a1.level_cup_cocycle-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data and define e(s,t)=φ(f(s),s·g(t)). This is exactly cupCochain φ f g. The two-cocycle differential is d₂e(s,t,u)=s·e(t,u)−e(st,u)+e(s,tu)−e(s,t).
2. Equivariance, the representation identity s·(t·b)=(st)·b, and the two one-cocycle identities give d₂e(s,t,u)=φ(s·f(t),(st)·g(u))−φ(s·f(t)+f(s),(st)·g(u))+φ(f(s),(st)·g(u)+s·g(t))−φ(f(s),s·g(t)). Expanding the second and third terms by bilinearity cancels φ(s·f(t),(st)·g(u)), φ(f(s),(st)·g(u)), and φ(f(s),s·g(t)), each with its negative. Thus d₂e=0 and e∈cocycles₂ N.
3. Choose witness fields Ff,Fg for the two level hypotheses. Set F=(E₀⊔Ff)⊔Fg. Applying IntermediateField.finiteDimensional_sup twice proves that F is finite-dimensional over ℚ. The inclusions E₀≤F, Ff≤F, and Fg≤F imply that every automorphism fixing F fixes each constituent field.
4. Let s,t,h,ℓ∈G with r(h),r(ℓ) fixing F. The witness conditions give f(sh)=f(s) and g(tℓ)=g(t). Since r(h) fixes E₀, the action hypothesis gives h·g(t)=g(t). Consequently e(sh,tℓ)=φ(f(sh),(sh)·g(tℓ))=φ(f(s),s·(h·g(t)))=φ(f(s),s·g(t))=e(s,t). Hence F witnesses IsLevelConstant₂ r e.
5. By definition, levelCocycles₂ r N is the intersection of cocycles₂ N with the submodule of level two-cochains. Steps 2 and 4 give both memberships, proving the conclusion.

## Key steps

1. Expand the cup differential using equivariance and the one-cocycle identities, then cancel by bilinearity.
2. Form the finite compositum (E₀⊔Ff)⊔Fg and restrict its fixing condition to all three fields.
3. Use the level identities and trivial action on B to prove two-variable level constancy.
4. Combine cocycle membership and level constancy to obtain membership in levelCocycles₂.

## Reference use

### local-project

Queries:
- `rg -n 'cupCochain|levelCocycles₁|levelCocycles₂|continuousH2π|H1π_eq_iff' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36 --glob '*.lean'`
- `rg -n 'finiteDimensional.*sup|finiteDimensional_sup|fixingSubgroup_antitone' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory`
- `rg -n 'continuous.*[Cc]up|[Cc]up.*continuous' .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions .humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/Galois/Basic.lean`

The manifest pins project 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. CupProduct provides the ordinary bilinear cup and both boundary-primitive calculations. ContinuousH1 is an image of level one-cocycles; ContinuousH2 uses the image of level one-cochains as its boundary denominator. H1π_eq_iff, finiteDimensional_sup, and fixingSubgroup_antitone support descent and common level fields. The focused continuous-cup search found no matching theorem. The three project definition files match the snapshot byte-for-byte, and the local mathlib checkout is clean at the pinned commit. Diagnostic axiom checks of the three proposed types and cited declarations found only propext, Classical.choice, and Quot.sound.
