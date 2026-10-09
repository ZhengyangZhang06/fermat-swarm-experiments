# Parent-supplied natural-language proof

- Parent DAG node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1`
- Child DAG node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.bialgebra_restriction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Give D its existing commutative ring and k-algebra structures, and denote its inclusion by i:D→H. Choose a k-basis of D. Its image under the injective linear map i is linearly independent in H, so extend that image to a basis of H. Define the linear map r:H→D by sending each original basis vector i(d) back to d and every added basis vector to zero. Linearity and the basis expansion give r(i(d))=d for all d in D.
2. Put J₂=i⊗i:D⊗D→H⊗H and J₃=i⊗(i⊗i):D⊗(D⊗D)→H⊗(H⊗H), with every tensor product over k. Their respective left inverses are r⊗r and r⊗(r⊗r): composition is the identity on pure tensors, hence on all tensors by linearity and generation by pure tensors. Thus both maps are injective. Moreover, the image of J₂ is precisely the span in the hypothesis. Indeed each tensor of D⊗D is a finite sum of pure tensors, so its image belongs to that span; conversely each generator a⊗b with a,b in D is J₂ applied to the corresponding pair of subtype elements, and the image is a linear subspace.
3. For d in D, the hypothesis and step 2 give a unique tensor δ(d) in D⊗D with J₂(δ(d))=Δ_H(i(d)). For d,e in D, applying J₂ to δ(d+e) and δ(d)+δ(e) gives the same result by linearity of Δ_H and i. Likewise its values on δ(c d) and c δ(d) agree for c in k, and its values on δ(0) and 0 agree. Injectivity of J₂ proves these equalities, so δ:D→D⊗D is k-linear.
4. J₂ is an algebra homomorphism: on pure tensors it sends (d⊗e)(d′⊗e′)=dd′⊗ee′ to the product of their images, and it sends 1⊗1 to 1⊗1; the multiplication equality extends to all tensors by bilinearity. Consequently J₂(δ(de))=Δ_H(i(d)i(e))=Δ_H(i(d))Δ_H(i(e))=J₂(δ(d)δ(e)), and J₂(δ(1))=Δ_H(1)=1=J₂(1). Injectivity shows that δ preserves multiplication and the unit. Together with linearity, this makes δ a k-algebra homomorphism for the existing algebra structure on D.
5. Define ε_D(d)=ε_H(i(d)). The inclusion and ε_H are k-linear and preserve multiplication and the unit, so ε_D has all these properties as well.
6. Write α_D:(D⊗D)⊗D→D⊗(D⊗D) and α_H for the associators. We verify coassociativity. For a finite expansion δ(d)=Σ_j a_j⊗b_j, applying J₃ to α_D((δ⊗id_D)δ(d)) gives Σ_j α_H(Δ_H(i(a_j))⊗i(b_j)); applying J₃ to (id_D⊗δ)δ(d) gives Σ_j i(a_j)⊗Δ_H(i(b_j)). These formulas follow from J₂δ=Δ_Hi, the pure-tensor formulas for tensor maps and associators, and linearity. Since Σ_j i(a_j)⊗i(b_j)=Δ_H(i(d)), these are exactly the left and right iterated coproducts of i(d). They are equal by coassociativity in H. Injectivity of J₃ proves α_D((δ⊗id_D)δ(d))=(id_D⊗δ)δ(d).
7. With the same finite expansion, the image under i of Σ_j ε_D(a_j)b_j is Σ_j ε_H(i(a_j))i(b_j)=i(d) by the left counit identity in H. The image of Σ_j ε_D(b_j)a_j is likewise i(d) by the right counit identity. Injectivity of i proves both sums equal d. Equivalently, under the canonical isomorphisms k⊗D≅D and D⊗k≅D, these are the two counit identities for δ and ε_D; applying the inverse isomorphisms gives their tensor-form identities.
8. The maps δ and ε_D therefore form a coalgebra, and steps 4–5 show its compatibility with multiplication and the unit. Package these data as bD:Bialgebra k D, retaining exactly the preexisting algebra structure, so bD.toAlgebra is that structure. Finally, the original inclusion preserves algebra operations, comultiplication by J₂δ=Δ_Hi, and counit by ε_D=ε_Hi. It is therefore a bialgebra homomorphism for bD, and its value at each d is the underlying element of H, as required.

## Key steps

1. Construct a linear retraction of the subalgebra inclusion by basis extension.
2. Prove double and triple tensor inclusions injective and identify the double tensor image.
3. Lift comultiplication uniquely and prove its linearity and algebra compatibility.
4. Restrict the counit and transfer coassociativity and both counit identities by injectivity.
5. Package the bialgebra with the unchanged algebra structure and the inclusion homomorphism.

## Reference use

### local-project

Queries:
- `injective|Injective|Subalgebra|Subcoalgebra|subalgebra|of_injective`
- `exists_leftInverse|leftInverse|map_injective|range_map|span_tmul|range.*[Tt]ensor|lift.*[Bb]ialgebra|[Ii]njective.*[Hh]opf|[Ss]ubalgebra.*[Bb]ialgebra`
- `injective.*hopf|hopf.*injective|stable.*[Ss]ubalgebra|[Ss]ubalgebra.*[Hh]opf|[Ss]ubalgebra.*[Bb]ialgebra|[Bb]ialgebra.*[Ss]ubalgebra`
- `p05_hte_sshs_bialgebra_restriction_a5b449214a|p05_hte_sshs_antipode_lift_a5b449214a`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Map.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Bialgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Bialgebra/Hom.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1/decomposition-sshs-diagnostics/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1/decomposition-sshs-diagnostics/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-stable-subalgebra-hopf-structure-a1/decomposition-sshs-diagnostics/CheckComposition.lean`

The snapshot supplies LinearMap.exists_leftInverse_of_injective, TensorProduct.range_map_eq_span_tmul, bialgebra constructors, and the two antipode identities. Searches found no matching subalgebra restriction or injective antipode-lifting theorem, and neither proposed identifier is reserved in the current DAG. Project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and all nine dependencies passed clean-pin checks. Both literal child types elaborate after import Submission in the derived challenge and solution contexts. Nine explicit instance probes passed; the antipode interface explicitly installs its new underlying bialgebra. An anonymous implication check verified that the two interfaces compose to the exact parent type. Nine infrastructure axiom closures contain only propext, Classical.choice and Quot.sound. The matching compiler-copy policy digest was checked; only listed lines 10–11 were omitted, reversible original/build hashes were validated, and Lean confirmed all 13 omitted targets absent. Protected inputs remain unchanged. These are decomposition diagnostics, not comparator acceptance of either child theorem.
