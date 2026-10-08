# Parent-supplied natural-language proof

- Parent DAG node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.bialgebra_restriction-a1`
- Child DAG node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.bialgebra_restriction-a1.comul_alg_lift-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Equip D with its existing subalgebra structures and write i:D→H for inclusion. Choose a k-basis (e_s) of D. Its image (i(e_s)) is linearly independent: any finite linear relation among these images is the image under the injective linear map i of the corresponding relation among the e_s. Extend this independent family to a basis of H. Define a k-linear map r:H→D by sending i(e_s) to e_s and every additional basis vector to zero. Expansion in the basis of D proves r(i(d))=d for every d∈D.
2. Define J=i⊗i:D⊗D→H⊗H and R=r⊗r. For every pure tensor d⊗e, R(J(d⊗e))=r(i(d))⊗r(i(e))=d⊗e. Since pure tensors span D⊗D and both maps are linear, R∘J is the identity. Therefore J is injective.
3. Let S=span_k{a⊗b | a∈D, b∈D}, viewed inside H⊗H. Every tensor in D⊗D is a finite sum of pure tensors, with scalar coefficients absorbed into a tensor factor. Its image under J consequently belongs to S, so range(J)⊆S. Conversely, each generator a⊗b of S is J applied to the tensor of the subtype elements determined by a∈D and b∈D. Since range(J) is a linear subspace, it contains S. Thus range(J)=S.
4. For every d∈D, the hypothesis applied to i(d) and step 3 show that Δ_H(i(d)) has a preimage under J. By step 2 this preimage is unique. Choose it and call it δ(d). Then J(δ(d))=Δ_H(i(d)) for every d.
5. The map δ is k-linear. Indeed J(δ(0))=0=J(0), so injectivity gives δ(0)=0. For d,e∈D, linearity of Δ_H and i gives J(δ(d+e))=Δ_H(i(d))+Δ_H(i(e))=J(δ(d)+δ(e)), hence δ(d+e)=δ(d)+δ(e). For c∈k, similarly J(δ(c•d))=c•Δ_H(i(d))=J(c•δ(d)), hence δ(c•d)=c•δ(d).
6. The map J is the algebra tensor map induced by i. Explicitly, for pure tensors its multiplicativity follows from (d⊗e)(d′⊗e′)=dd′⊗ee′ and the multiplicativity of i. Distributivity and finite pure-tensor expansions extend this equality to arbitrary pairs of tensors. It also sends 1_D⊗1_D to 1_H⊗1_H, the respective tensor-algebra units. Thus J preserves multiplication and the unit.
7. Because Δ_H is an algebra homomorphism, for d,e∈D we have J(δ(de))=Δ_H(i(d)i(e))=Δ_H(i(d))Δ_H(i(e))=J(δ(d)δ(e)). Injectivity gives δ(de)=δ(d)δ(e). Likewise J(δ(1))=Δ_H(1)=1=J(1), so δ(1)=1. Together with step 5 these make δ a unital multiplicative k-linear map. It respects the existing algebra maps because δ(c•1_D)=c•δ(1_D)=c•1_{D⊗D}. Hence δ is a k-algebra homomorphism for the prescribed structures. Its defining equality from step 4 is the required conclusion.

## Key steps

1. Construct a k-linear retraction of the subalgebra inclusion by extending a basis.
2. Tensor the retraction to prove injectivity of i⊗i.
3. Identify the image of i⊗i with the stipulated span of pure tensors.
4. Choose the unique lift of each ambient coproduct.
5. Cancel i⊗i to establish linearity of the lifted map.
6. Use multiplicativity and unitality of the tensor inclusion and ambient coproduct to establish the algebra-homomorphism laws.

## Reference use

### local-project

Queries:
- `ofInjective|of_injective|map_injective|range.*map|span.*tmul|subalgebra|Subalgebra`
- `theorem.*[iI]njective|lemma.*[iI]njective|def.*[lL]eftInverse`
- `bialgebra_restriction|comul.*[lL]ift|[cC]oalgebra.*[iI]njective|[bB]ialgebra.*[iI]njective`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Map.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Bialgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Bialgebra/Hom.lean`

The manifest pins project 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. VectorSpace.lean supplies LinearMap.exists_leftInverse_of_injective; Map.lean supplies TensorProduct.range_map_eq_span_tmul. Coalgebra.Basic gives exactly the three tensor identities needed below, while Bialgebra.mk' and BialgHom.ofAlgHom provide the final packaging. No relevant injective coalgebra-transfer or subalgebra bialgebra-restriction constructor was found; the nearby lifting match constructs a quotient coalgebra. Relevant snapshot sources match the pinned compiler dependencies. Axiom checks on the retraction and range lemmas, Algebra.TensorProduct.map, AlgHom.ofLinearMap, Coalgebra.mk, Bialgebra.mk', and BialgHom.ofAlgHom reported only propext, Quot.sound, and Classical.choice.
