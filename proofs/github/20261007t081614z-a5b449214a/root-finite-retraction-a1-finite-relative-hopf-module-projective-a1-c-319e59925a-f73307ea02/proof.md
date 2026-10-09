# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1.algebra_coaction_twist-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put S=A⊗_k H and denote the antipode and counit of A by S_A and ε_A. Write Δ_A(a)=Σa₁⊗a₂. Such notation abbreviates a finite tensor representation. Every expression below is obtained by applying linear maps induced by multiplication, ι and S_A, so its value is independent of the chosen representation.
2. Define prescriptions F(a,h)=Σa₁⊗ι(a₂)h and G(a,h)=Σa₁⊗ι(S_A(a₂))h. Explicitly, F(a,h)=((id_A⊗ι)(Δ_A(a)))(1⊗h), and G uses ι∘S_A in place of ι. Comultiplication, ι, S_A and h↦1⊗h are k-linear, while multiplication in S is k-bilinear. Hence F and G are separately k-linear in a and h. The tensor universal property therefore gives k-linear maps θ₀,ψ:S→S with θ₀(a⊗h)=F(a,h) and ψ(a⊗h)=G(a,h).
3. Since Δ_A and ι preserve multiplication, for a,b∈A and h,g∈H we have θ₀((a⊗h)(b⊗g))=Σa₁b₁⊗ι(a₂b₂)hg. Tensor-product multiplication gives θ₀(a⊗h)θ₀(b⊗g)=Σa₁b₁⊗(ι(a₂)h)(ι(b₂)g). Multiplicativity of ι and commutativity of H identify these two sums. Both sides of θ₀(xy)=θ₀(x)θ₀(y) are separately k-linear in x and y. Every tensor is a finite sum of pure tensors, so the equality holds for all x,y∈S.
4. Comultiplication and ι preserve the unit, hence θ₀(1⊗1)=1⊗1. Together with k-linearity this implies θ₀(c·1)=c·1 for every c∈k. Thus θ₀ is a unital k-algebra homomorphism.
5. Expanding θ₀ψ on a pure tensor gives Σ(a₁)₁⊗ι((a₁)₂)ι(S_A(a₂))h. Apply coassociativity of Δ_A, followed by the linear map sending x⊗y⊗z to x⊗ι(yS_A(z))h. This rewrites the result as Σa₁⊗ι((a₂)₁S_A((a₂)₂))h. The antipode identity Σb₁S_A(b₂)=ε_A(b)·1_A, and preservation of scalars by ι, reduce it to Σa₁⊗(ε_A(a₂)·h). Tensor balancing changes this to (Σ ε_A(a₂)·a₁)⊗h, which equals a⊗h by right counitality.
6. Expanding ψθ₀ gives Σ(a₁)₁⊗ι(S_A((a₁)₂))ι(a₂)h. Coassociativity, now followed by x⊗y⊗z↦x⊗ι(S_A(y)z)h, rewrites this as Σa₁⊗ι(S_A((a₂)₁)(a₂)₂)h. The other antipode identity ΣS_A(b₁)b₂=ε_A(b)·1_A reduces it to the same counit expression as in step 5, hence to a⊗h.
7. Both compositions θ₀ψ and ψθ₀ are k-linear and agree with the identity on every pure tensor. They consequently equal the identity on all of S. Thus θ₀ is bijective, with inverse ψ. The bijective k-algebra homomorphism θ₀ defines a k-algebra automorphism θ. Its value on each a⊗h is the formula from step 2, exactly as required.

## Key steps

1. Construct θ₀ and its antipode-based candidate inverse ψ by the tensor universal property.
2. Prove θ₀ multiplicative on pure tensors and extend in both arguments.
3. Prove preservation of the unit and embedded k-scalars.
4. Use coassociativity and the id–antipode cancellation identity to show θ₀ψ=id.
5. Use coassociativity and the antipode–id cancellation identity to show ψθ₀=id.
6. Bundle the bijective algebra homomorphism as θ with the required formula.

## Reference use

### local-project

Queries:
- `Repr.arbitrary|coassociat|semilinear|tensor.*equiv|exists.*twist|antipode`
- `coassoc|counit.*rTensor|rTensor.*counit|arbitrary|sum_tmul`
- `coaction.*(twist|equiv)|twist.*(coaction|tensor)|p05_ct_(algebra|comodule|compatibility)_a5b449214a`
- `theorem tmul_mul_tmul|lemma tmul_mul_tmul|instance.*CommRing|def mulLeft`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean`

The project defines the induced algebra coaction. Coalgebra.Basic provides finite representations, coassociativity and counitality; HopfAlgebra.Basic provides both antipode cancellation identities; TensorProduct.Basic supplies tensor multiplication. No existing coaction-twist equivalence matched the search in the project and HopfAlgebra reference sources. Snapshot revisions match the manifest and are clean; installed dependency revisions also match their pins. Both proposed types elaborated after import Submission using Lean 4.33.1 in /tmp/p05-coaction-decomposition-h39p315q. The inferred multiplication was checked against Algebra.TensorProduct.tmul_mul_tmul. The inspected cancellation, coassociativity, counit and tensor-map declarations have only standard logical axioms. Private-copy header omissions matched the specified policy, and a fresh Lean probe confirmed all 13 omitted targets absent. These are decomposition diagnostics, not proof acceptance.
