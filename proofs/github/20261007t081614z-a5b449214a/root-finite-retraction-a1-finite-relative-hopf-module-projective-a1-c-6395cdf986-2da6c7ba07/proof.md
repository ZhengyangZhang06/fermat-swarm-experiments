# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.coaction_twist-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. All tensor products below are over k. Write Δ_A(a)=Σa_1⊗a_2 and μ(m)=Σm_0⊗m_1. Expressions using these finite sums are representation-independent: each is obtained from the tensor itself by composing linear maps induced by the displayed bilinear multiplications or actions. In particular, the given Coalgebra.Repr.arbitrary compatibility becomes the stated Sweedler formula.
2. Define k-linear maps θ_0,ψ:S→S on pure tensors by θ_0(a⊗h)=Σa_1⊗ι(a_2)h and ψ(a⊗h)=Σa_1⊗ι(S_A(a_2))h. Each prescription is k-bilinear in a,h, so the tensor universal property gives the claimed maps. Multiplicativity of Δ_A and ι gives θ_0((a⊗h)(b⊗g))=Σa_1b_1⊗ι(a_2b_2)hg=θ_0(a⊗h)θ_0(b⊗g). Bilinearity extends this equality to arbitrary tensors. Also θ_0(1⊗1)=1⊗1, and k-linearity then shows that θ_0 preserves the embedded k-scalars.
3. By coassociativity, θ_0ψ(a⊗h)=Σa_1⊗ι(a_2 S_A(a_3))h and ψθ_0(a⊗h)=Σa_1⊗ι(S_A(a_2)a_3)h. In the first expression apply the antipode identity multiplying the last two factors in the order id⊗S; in the second use S⊗id. Each expression becomes Σa_1⊗ε_A(a_2)h=a⊗h by counitality and k-balancing. The equalities hold on all tensors by linearity. Thus ψ is a two-sided inverse to θ_0, and θ_0 defines the required k-algebra automorphism θ. Its asserted formula is exactly its definition, using tensor-product multiplication.
4. Define k-linear maps T_0,U:W→W on pure tensors by T_0(m⊗h)=Σm_0⊗m_1h and U(m⊗h)=Σm_0⊗S_H(m_1)h. Both prescriptions are k-bilinear in m,h, since μ and the antipode are k-linear and multiplication is bilinear, so both descend to the tensor product.
5. Coassociativity of μ rewrites T_0U(m⊗h) as Σm_0⊗m_1S_H(m_2)h, and UT_0(m⊗h) as Σm_0⊗S_H(m_1)m_2h. The two antipode identities reduce these to Σm_0⊗ε_H(m_1)h. The assumed counitality of μ and k-balancing identify this with m⊗h. Hence T_0 and U are mutually inverse on pure tensors and therefore everywhere. They define a k-linear automorphism T. Since H is commutative, m_1h=hm_1, which is precisely the pure-tensor formula for T demanded in the statement.
6. For a∈A, h,g∈H and m∈M, the supplied S-action and compatibility of μ give T((a⊗h)·(m⊗g))=Σa_1·m_0⊗ι(a_2)m_1hg. On the other hand θ(a⊗h)·T(m⊗g)=Σa_1·m_0⊗(ι(a_2)h)(m_1g), using the same supplied action on each pure tensor. Commutativity and associativity in H equate these expressions. Both sides are additive separately in the scalar tensor and the module tensor; expressing arbitrary tensors as finite sums of pure tensors therefore proves T(s·x)=θ(s)·T(x) for all s,x. Together with steps 3 and 5, this proves every part of the existential conclusion.

## Key steps

1. Interpret the compatibility formula through the tensor universal property.
2. Construct the algebra twist and its inverse using Δ_A and S_A.
3. Use antipode and counit identities to prove the algebra twist invertible.
4. Construct the coaction twist and its inverse using μ and S_H.
5. Use coassociativity and counitality to prove the module twist invertible.
6. Check semilinearity on pure tensors and extend by additivity.

## Reference use

### local-project

Queries:
- `Fitting|fittingIdeal|fitting_ideal|FinitePresentation|antipode_mul|antipode.*AlgHom`
- `fitting`
- `antipode.*(mul|AlgHom)|map_mul.*antipode|antipodeAlgHom`
- `injective.*exists|exists.*leftInverse|leftInverse`
- `det.*map|map.*det`
- `isNoetherianRing`
- `def hopfKer|hopfKer|equalizer`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`

The snapshots are clean at project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d; all nine dependency checkouts match their clean pins. Relevant infrastructure includes finite presentations, tensor right exactness, tensor algebra operations, antipode identities, linear retractions, and determinants commuting with ring maps. The case-insensitive Fitting search in mathlib/RingTheory and project/Definitions found only unrelated Artinian-module decomposition results, not a Fitting-ideal API. All four proposed types elaborate after import Submission; anonymous checks verify tensor multiplication, scalar action, inclusion, and matrix-vector semantics. Nine inspected infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. No proposed name collides with the scanned DAG reservations or Submission. Policy-compliant diagnostics are recorded in /tmp/p05-rhm-decomp-hlprok3k: header-input-binding.json binds policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, exactly omitted lines 10–11, and reversible original/build hashes; Absence.lean.log confirms all 13 targets absent under the frozen imports. Protected files remain unchanged. These are interface diagnostics, not comparator acceptance of any theorem.
