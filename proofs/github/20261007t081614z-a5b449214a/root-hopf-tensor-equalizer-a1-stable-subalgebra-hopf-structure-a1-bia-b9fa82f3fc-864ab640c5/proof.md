# Parent-supplied natural-language proof

- Parent DAG node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.bialgebra_restriction-a1`
- Child DAG node: `root.hopf_tensor_equalizer-a1.stable_subalgebra_hopf_structure-a1.bialgebra_restriction-a1.coalgebra_law_descent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Choose a k-basis (e_s) of V. Injectivity and linearity of i imply that (i(e_s)) is linearly independent in C: applying injectivity to any finite relation among these images reduces it to the corresponding relation among the e_s. Extend this family to a basis of C. Send each i(e_s) back to e_s and the additional basis vectors to zero, and extend linearly to obtain r:C→V. Basis expansion gives r∘i=id_V.
2. Define J₂=i⊗i, J₃=i⊗(i⊗i), L=id_k⊗i, and R=i⊗id_k. These have respective left inverses r⊗r, r⊗(r⊗r), id_k⊗r, and r⊗id_k. Each claimed composition is the identity on pure tensors; for J₃ use generators x⊗(y⊗z). Such tensors span their domains, so linearity proves all four left-inverse identities. In particular J₃, L, and R are injective.
3. Let α_C be the associator for C. We establish the naturality identities J₃∘α_V∘(δ⊗id_V)=α_C∘(Δ_C⊗id_C)∘J₂ and J₃∘(id_V⊗δ)=(id_C⊗Δ_C)∘J₂ as maps from V⊗V to C⊗(C⊗C). For the first, evaluate at x⊗y and write δ(x)=Σ_p u_p⊗w_p. Its left side is Σ_p i(u_p)⊗(i(w_p)⊗i(y)), which equals α_C(J₂(δ(x))⊗i(y))=α_C(Δ_C(i(x))⊗i(y)) by the compatibility hypothesis. This is its right side at x⊗y. For the second, expand δ(y) into pure tensors; its left side becomes i(x)⊗J₂(δ(y))=i(x)⊗Δ_C(i(y)), again its right side. Equality on pure tensors extends to all tensors by linearity.
4. Fix v∈V and apply the identities of step 3 to δ(v). Since J₂(δ(v))=Δ_C(i(v)), they identify the images under J₃ of α_V((δ⊗id_V)(δ(v))) and (id_V⊗δ)(δ(v)) with α_C((Δ_C⊗id_C)(Δ_C(i(v)))) and (id_C⊗Δ_C)(Δ_C(i(v))), respectively. These ambient expressions are equal by coassociativity in C. Injectivity of J₃ proves the required coassociativity identity in V for every v.
5. On a pure tensor x⊗y, L((ε⊗id_V)(x⊗y))=ε(x)⊗i(y)=ε_C(i(x))⊗i(y)=(ε_C⊗id_C)(J₂(x⊗y)). Thus L∘(ε⊗id_V)=(ε_C⊗id_C)∘J₂ by linearity. Evaluating at δ(v), using coproduct compatibility and the left counit identity in C, gives L((ε⊗id_V)(δ(v)))=(ε_C⊗id_C)(Δ_C(i(v)))=1⊗i(v)=L(1⊗v). Injectivity of L proves (ε⊗id_V)(δ(v))=1⊗v for every v.
6. Likewise, on x⊗y we have R((id_V⊗ε)(x⊗y))=i(x)⊗ε(y)=i(x)⊗ε_C(i(y))=(id_C⊗ε_C)(J₂(x⊗y)). Extend this equality linearly and evaluate at δ(v). The right counit identity in C yields R((id_V⊗ε)(δ(v)))=(id_C⊗ε_C)(Δ_C(i(v)))=i(v)⊗1=R(v⊗1). Injectivity of R proves (id_V⊗ε)(δ(v))=v⊗1 for every v. Together with steps 4 and 5 this establishes all three stated identities.

## Key steps

1. Construct a linear retraction of the injective map i by basis extension.
2. Obtain injectivity of the triple tensor map and the two unit-factor tensor maps.
3. Verify coproduct and associator naturality on pure tensors and extend linearly.
4. Transport ambient coassociativity and cancel the triple tensor inclusion.
5. Transport the left counit identity and cancel id_k⊗i.
6. Transport the right counit identity and cancel i⊗id_k.

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
