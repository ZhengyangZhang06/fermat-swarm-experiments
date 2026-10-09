# Parent-supplied natural-language proof

- Parent DAG node: `root.canonical_map_injective-a1`
- Child DAG node: `root.canonical_map_injective-a1.translation_left_inverse-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write S and ε for the antipode and counit. The map i:H→T given by i(a)=a⊗_K1_H is a k-algebra homomorphism, by the tensor multiplication and scalar formulas. Since σ is also a k-algebra homomorphism, the formula G(a,c)=i(a)σ(c) is k-bilinear. The tensor-product universal property gives a k-linear map γ:U→T satisfying γ(a⊗_k c)=(a⊗_K1_H)σ(c).
2. For pure tensors, multiplicativity of i and σ and commutativity of T give γ((a⊗c)(a′⊗c′))=i(aa′)σ(cc′)=i(a)σ(c)i(a′)σ(c′). Additivity and distributivity extend this equality to arbitrary tensors. Also γ(1_H⊗1_B)=i(1_H)σ(1_B)=1_T. The k-linearity of γ then implies preservation of k-scalars. Thus γ is a k-algebra homomorphism with the required formula.
3. Establish the cancellation identity Σb₁S(b₂)⊗_k b₃=1_H⊗_k b. Apply the linear map that multiplies the first factor by the antipode of the second factor and retains the third factor to (Δ_H⊗id_H)Δ_H(b). The antipode identity turns the result into ΣalgebraMap(k,H)(ε(b₁))⊗_k b₂. Moving each k-scalar to the second factor and using the left counit identity turns this into 1_H⊗_k b. Coassociativity permits the same identity to be read using (id_H⊗Δ_H)Δ_H(b). All displayed sums are finite tensor representations of these linear-map identities.
4. Fix a,b∈H. The hypothesis on β and the definition of ρ give β(a⊗_K b)=Σab₁⊗_k q(b₂). Apply γ, then its pure-tensor formula and the hypothesis on σ. This gives γβ(a⊗_K b)=Σ(ab₁⊗_K1_H)C((S⊗id_H)Δ_H(b₂))=Σab₁S(b₂)⊗_K b₃, where coassociativity identifies the nested comultiplications. Map the identity from step 3 through C and multiply by a⊗_K1_H. The resulting equality is exactly γβ(a⊗_K b)=a⊗_K b.
5. Both γβ and the identity on T are additive. Every element of T is a finite sum of pure tensors, so step 4 implies γ(β(z))=z for every z∈T. Thus γ is a left inverse of β. Together with its formula from step 1, it satisfies both required conjuncts.

## Key steps

1. Construct γ from the bilinear formula using the supplied translation homomorphism.
2. Verify that γ is an algebra homomorphism.
3. Derive the three-factor antipode cancellation identity from coassociativity and the counit law.
4. Expand γβ on pure tensors using the two supplied formulas.
5. Apply cancellation and extend by additivity to obtain the left-inverse identity.

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
