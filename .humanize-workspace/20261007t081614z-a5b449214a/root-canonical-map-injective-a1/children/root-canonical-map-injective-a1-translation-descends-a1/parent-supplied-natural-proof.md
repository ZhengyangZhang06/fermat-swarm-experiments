# Parent-supplied natural-language proof

- Parent DAG node: `root.canonical_map_injective-a1`
- Child DAG node: `root.canonical_map_injective-a1.translation_descends-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put T=H⊗_K H and write S and ε for the antipode and counit of H. The formula C(a⊗_k b)=a⊗_K b defines a k-linear map because the K-balancing relations include the k-balancing relations. The tensor multiplication formula shows that C preserves products on pure tensors, hence on all tensors by additivity. It preserves 1⊗1 and therefore k-scalars, so C is a k-algebra homomorphism.
2. The antipode S is a k-algebra homomorphism. Here is the convolution argument establishing the needed multiplicativity. For k-linear maps u,v:H⊗_k H→H define (u*v)(a⊗b)=Σu(a₁⊗b₁)v(a₂⊗b₂). All Sweedler sums denote finite tensor representations. Coassociativity identifies both parenthesizations of a triple convolution with Σu(a₁⊗b₁)v(a₂⊗b₂)w(a₃⊗b₃). Thus convolution is associative; the counit identities show its unit is e(a⊗b)=ε(a)ε(b)1_H. Define f(a⊗b)=ab, g(a⊗b)=S(ab), and h(a⊗b)=S(a)S(b). These formulas are bilinear and therefore define linear maps. Multiplicativity of Δ and the antipode identity applied to ab give (g*f)(a⊗b)=ΣS(a₁b₁)a₂b₂=ε(ab)1_H=e(a⊗b). Commutativity of H and the antipode identities give (f*h)(a⊗b)=Σa₁b₁S(a₂)S(b₂)=(Σa₁S(a₂))(Σb₁S(b₂))=e(a⊗b). Equality on pure tensors gives g*f=e and f*h=e as linear maps. Consequently g=g*(f*h)=(g*f)*h=h. This proves S(ab)=S(a)S(b). The antipode identity at 1 gives S(1)=1. Since S is k-linear, it also preserves k-scalars.
3. Define τ=C∘(S⊗id_H)∘Δ_H. Each factor is a k-algebra homomorphism by step 2 and the tensor-algebra multiplication formula. Hence τ:H→T is a k-algebra homomorphism, and its value on b is precisely C((S⊗id_H)Δ_H(b)).
4. Fix t∈K. By hΔ, write Δ_H(t)=Σ_i a_i⊗_k b_i with a_i,b_i∈K. This follows from the definition of linear span, absorbing each scalar coefficient into a_i, which remains in K. By hS, S(a_i)∈K. Balancing therefore gives S(a_i)⊗_K b_i=1_H⊗_K S(a_i)b_i. Summing and applying the antipode identity yields τ(t)=1_H⊗_K algebraMap(k,H)(ε(t)). This is the k-scalar image of ε(t) in T.
5. If t∈K and ε(t)=0, step 4 gives τ(t)=0. The ring kernel of τ is an ideal containing every generator in the stated ideal span. Thus it contains that ideal span. By hker, ker(q)⊆ker(τ).
6. For c∈B, surjectivity supplies b∈H with q(b)=c. Define σ(c)=τ(b). If b′ is another such lift, then q(b−b′)=0. Step 5 implies τ(b−b′)=0, hence τ(b)=τ(b′). Thus the definition is independent of the chosen lift.
7. For c,d∈B choose lifts b,b′. Then b+b′ and bb′ lift c+d and cd, so σ(c+d)=τ(b+b′)=σ(c)+σ(d) and σ(cd)=τ(bb′)=σ(c)σ(d). The elements 0_H and 1_H lift 0_B and 1_B, giving σ(0)=0 and σ(1)=1. For λ∈k, algebraMap(k,H)(λ) lifts algebraMap(k,B)(λ); preservation of scalars by τ gives preservation of scalars by σ. Consequently σ is a k-algebra homomorphism.
8. For any b∈H, b itself is a lift of q(b). Independence of lifts gives σ(q(b))=τ(b). Substituting the definition in step 3 proves the required formula.

## Key steps

1. Construct the canonical k-algebra map from the tensor product over k to the tensor product over K.
2. Establish antipode multiplicativity by uniqueness of convolution inverses.
3. Construct the translation algebra homomorphism τ.
4. Use comultiplication closure, antipode closure, and balancing to compute τ on K.
5. Show τ kills the augmentation generators and hence ker(q).
6. Descend τ through the surjection q using independence of lifts.
7. Verify the descended algebra homomorphism and its prescribed values on q(H).

## Reference use

### local-project

Queries:
- `antipode|coaction|hopfKer|TensorProduct`
- `antipode.*(mul|AlgHom)|baseChange|lift.*[Aa]lgHom|liftOf|ofSurjective|ker_le`
- `def (lift|map|includeLeft|includeRight)|lift_tmul|map_tmul|ofTower|tensor.*[Tt]ower|algebraMap_def`
- `p05_canonical_balanced_lift_a5b449214a|p05_translation_descends_a5b449214a|p05_translation_left_inverse_a5b449214a`
- `rg --files -uu -g dag.json /mnt/data/zhengyang-workspace/fermat-swarm-projects`
- `python3 .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/validate.py`
- `python3 .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/rerun_instances.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/TensorProduct/Maps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/CheckInstances.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/header-input-binding.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-canonical-map-injective-a1/split-validation/report.json`

The snapshot provides coaction, antipodeAlgHom, tensor-algebra lifting, and mapOfCompatibleSMul; these require no new helper declarations. Project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and all nine dependency checkouts passed cleanliness and identity checks. Searches found no proposed-name collisions in the pinned Lean sources or local DAGs. All three literal child types elaborate after import Submission. Separate Lean probes verified inclusion actions, tensor multiplication, units, scalars, and the scalar-changing map. Eight infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. Disposable compiler copies followed the matching policy entry with digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: only lines 10–11 were omitted, reversible hashes were checked, and Lean confirmed all 13 targets absent. Frozen originals and the reviewed handoff remained unchanged. These are decomposition diagnostics; theorem acceptance still requires the configured comparator and independent review.
