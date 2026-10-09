# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1.comodule_coaction_twist-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put W=M⊗_k H and denote the antipode and counit of H by S_H and ε_H. Write μ(m)=Σm₀⊗m₁. These are finite tensor sums. Applying linear maps to μ(m) makes all expressions below independent of their finite representations.
2. Define F(m,h)=Σm₀⊗m₁h and G(m,h)=Σm₀⊗S_H(m₁)h. For fixed h these are compositions of μ with tensor maps induced by k-linear maps on H. For fixed m, additivity and k-homogeneity in h follow from bilinearity of multiplication in H and of the tensor product. Thus F and G are k-bilinear. The tensor universal property gives k-linear maps T₀,U:W→W satisfying T₀(m⊗h)=F(m,h) and U(m⊗h)=G(m,h).
3. The assumed coassociativity is the tensor identity Σ(m₀)₀⊗(m₀)₁⊗m₁=Σm₀⊗(m₁)₁⊗(m₁)₂, with the left side transported by the associator. For fixed h, the prescriptions x⊗y⊗z↦x⊗yS_H(z)h and x⊗y⊗z↦x⊗S_H(y)zh define linear maps on the threefold tensor product: each prescription is k-multilinear. We may therefore apply either map to this identity.
4. Expanding the first composition gives T₀U(m⊗h)=Σ(m₀)₀⊗(m₀)₁S_H(m₁)h. Apply the first linear map from step 3 to coassociativity to obtain Σm₀⊗(m₁)₁S_H((m₁)₂)h. The Hopf identity Σb₁S_H(b₂)=ε_H(b)·1_H reduces this to Σm₀⊗(ε_H(m₁)·h).
5. Expanding the other composition gives UT₀(m⊗h)=Σ(m₀)₀⊗S_H((m₀)₁)m₁h. Apply the second linear map from step 3 to coassociativity to obtain Σm₀⊗S_H((m₁)₁)(m₁)₂h. The Hopf identity ΣS_H(b₁)b₂=ε_H(b)·1_H reduces this to the same expression Σm₀⊗(ε_H(m₁)·h).
6. Tensor balancing and additivity identify that common expression with (Σ ε_H(m₁)·m₀)⊗h. By the defining formula for rid, the first tensor factor is rid((id_M⊗ε_H)(μ(m))), which equals m by the assumed counitality. Thus both compositions fix every pure tensor m⊗h. Since both compositions are k-linear and pure tensors span W, T₀U=id_W and UT₀=id_W on all of W.
7. The mutually inverse k-linear maps T₀ and U define a k-linear automorphism T with forward map T₀. Commutativity of H gives m₁h=hm₁, so T(m⊗h)=Σm₀⊗hm₁=(id_M⊗L_h)(μ(m)). This is precisely the asserted formula.

## Key steps

1. Construct T₀ and U from the coaction and antipode using bilinearity.
2. Express the coassociativity hypothesis as an equality of threefold tensor sums.
3. Rewrite T₀U and apply the id–antipode Hopf identity.
4. Rewrite UT₀ and apply the antipode–id Hopf identity.
5. Apply tensor balancing and the assumed counitality, then extend from pure tensors.
6. Bundle the inverse linear maps and use commutativity to obtain the left-multiplication formula.

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
