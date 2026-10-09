# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.twisted_presentation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define A(b)_i=θ⁻¹(b_i) for b∈S^n and define qθ(b)=T(q(A(b))). The maps A, q and T are additive, so qθ is additive. For s∈S, A(sb)=θ⁻¹(s)A(b). S-linearity of q and the assumed semilinearity of T give qθ(sb)=T(θ⁻¹(s)q(A(b)))=θ(θ⁻¹(s))T(q(A(b)))=s qθ(b). Hence the displayed formula defines an S-linear map qθ and proves its asserted value on every tuple.
2. For y∈L, surjectivity of q supplies a∈S^n with q(a)=T⁻¹(y). Set b_i=θ(a_i). Then A(b)=a and qθ(b)=T(T⁻¹(y))=y. Therefore qθ is surjective.
3. Put Pθ=P.map θ.toRingHom, and interpret application of θ or θ⁻¹ to a tuple coordinatewise. Since θ preserves finite sums and products, every c∈S^p satisfies θ((Pc)_i)=Σ_j θ(P_ij)θ(c_j)=(Pθ(θ(c)))_i. Applying θ⁻¹ likewise gives A(Pθ d)=P(θ⁻¹(d)) for every d∈S^p. These identities also hold for empty index sets.
4. Additivity gives T(0)=0, and T is injective. Therefore qθ(b)=0 if and only if q(A(b))=0. The equality ker(q)=im(P) makes this equivalent to A(b)=Pc for some c∈S^p. Applying θ coordinatewise and using step 3 gives b=Pθ(θ(c)), so b∈im(Pθ).
5. Conversely, if b=Pθ d, the inverse identity in step 3 gives A(b)=P(θ⁻¹(d)). This belongs to im(P)=ker(q), so qθ(b)=T(0)=0. Both containments establish ker(qθ)=im(Pθ). Together with the formula and surjectivity proved in steps 1 and 2, this establishes the full conclusion.

## Key steps

1. Conjugate coefficient vectors by θ⁻¹ and compose with q and T.
2. Use semilinearity to prove the resulting map is S-linear.
3. Construct a preimage of any element using q's surjectivity and the inverse of T.
4. Establish coordinatewise compatibility of θ with matrix-vector multiplication.
5. Use injectivity of T and the original kernel equality to prove both inclusions for the twisted kernel.

## Reference use

### local-project

Queries:
- `determinantal|fittingideal|fitting ideal`
- `rTensor_exact|lTensor_exact|map_det|map_span|baseChange.*surjective|baseChange.*exact`
- `def mulVecLin|mulVecLin_apply|def hopfKer|theorem hopfKer`
- `smul_tmul|tmul_smul`
- `rg --files -uu /mnt/data/zhengyang-workspace/fermat-swarm-projects -g dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Ideal/Maps.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p05-bcsi-decomp-va00aen4/CheckTypes.lean`
- `/tmp/p05-bcsi-decomp-va00aen4/CheckTypes.lean.log`
- `/tmp/p05-bcsi-decomp-va00aen4/Absence.lean.log`
- `/tmp/p05-bcsi-decomp-va00aen4/header-input-binding.json`
- `/tmp/p05-bcsi-decomp-va00aen4/report.json`

The clean snapshots match project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d; all nine compiler dependency checkouts match their clean pins. The targeted determinantal/Fitting-ideal search found no matching API in mathlib's LinearAlgebra and RingTheory directories. Relevant infrastructure includes lTensor_exact, LinearMap.baseChange_surjective, Matrix.mulVecLin_apply, RingHom.map_det, and Ideal.map_span. Both literal child types elaborate after import Submission at the fixed proof-base ca1bb49d173a82f6c760dd27fdde39c92765501e. Anonymous proofs verify the first-factor S-action and both mapped matrix-vector formulas. Six inspected infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. Neither proposed name collides with the ten scanned active DAGs or current Submission. Disposable compiler copies omit exactly policy-listed lines 10–11 under policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; Lean confirms all 13 targets absent, and reversible original/build hashes are recorded. The frozen contract and Submission header remain intact. These are interface diagnostics, not comparator acceptance of a theorem.
