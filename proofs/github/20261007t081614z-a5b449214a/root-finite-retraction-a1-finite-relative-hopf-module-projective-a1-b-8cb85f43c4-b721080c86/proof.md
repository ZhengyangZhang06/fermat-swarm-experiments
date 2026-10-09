# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.base_change_semilinear_invariance-a1.base_changed_presentation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write φ for the algebra map, let e_i denote standard coordinate vectors, put m_i=π(e_i), and let P_S be P with φ applied entrywise. Define q(b)=Σ_i b_i·(1⊗m_i). Distributivity and associativity of the first-factor S-action show q(b+b')=q(b)+q(b') and q(sb)=s q(b). Thus q is an S-linear map with the asserted formula.
2. For m∈M choose a∈R^n with π(a)=m. The coordinate identity a=Σ_i a_i e_i implies m=Σ_i a_i m_i. Tensor additivity and balancing give s⊗m=Σ_i sφ(a_i)·(1⊗m_i). This equals q applied to the tuple with coordinates sφ(a_i). Every tensor is a finite sum of pure tensors, and the image of q is closed under sums. Therefore q is surjective.
3. Let N=im(P_S). For each column j, let f_j be the corresponding standard vector in the domain of the matrix. The hypothesis im(P)=ker(π) gives π(Pf_j)=0. Consequently q(P_S f_j)=Σ_i φ(P_ij)·(1⊗m_i)=1⊗π(Pf_j)=0, using the standard vector over the appropriate coefficient ring in each occurrence. Every P_S c is the sum of c_j times these columns, so N⊆ker(q). Hence q induces an S-linear map α:C→S⊗_R M on C=S^n/N, with α([b])=q(b).
4. Regard C as an R-module via φ and define v:R^n→C by v(a)=[(φ(a_i))_i]. This map is R-linear. If a=Pd, preservation of sums and products by φ gives (φ(a_i))_i=P_S(φ(d_j))_j, so v(a)=0. Thus v kills ker(π). Define β(m)=v(a) for any lift π(a)=m. Two lifts differ by an element of ker(π), so this definition is independent of the lift. Using lifts a+a' and ra proves additivity and R-linearity of β. In particular β(m_i)=[e_i], now with e_i the standard vector over S.
5. The map (s,m)↦s·β(m) is additive in both arguments and R-balanced: s·β(rm)=sφ(r)·β(m). The tensor universal property therefore gives β̂:S⊗_R M→C with β̂(s⊗m)=s·β(m). Multiplication of the first tensor factor by t multiplies this image by t. Since pure tensors generate, β̂ is S-linear.
6. For every i, β̂α([e_i])=β̂(1⊗m_i)=β(m_i)=[e_i]. The classes [e_i] generate C over S, so β̂α is the identity. Conversely αβ̂(s⊗m_i)=α(s[e_i])=s·(1⊗m_i)=s⊗m_i. Step 2 expresses every pure tensor as an S-linear combination of the 1⊗m_i, so αβ̂ is also the identity. In particular α is injective.
7. Since q(b)=α([b]) and α is injective, q(b)=0 if and only if [b]=0, which is equivalent to b∈N. Therefore ker(q)=im(P_S). Together with steps 1 and 2, this proves every clause of the conclusion. All coordinate identities and sums used above remain valid when n or p is zero.

## Key steps

1. Define the canonical S-linear map from the images of the standard generators.
2. Use surjectivity of π and tensor balancing to prove surjectivity of q.
3. Show the mapped relation columns vanish and descend q to their cokernel.
4. Factor the coordinatewise algebra-map quotient through π to construct β.
5. Extend β by the balanced tensor universal property.
6. Check the two induced maps are inverse on generating elements.
7. Deduce the exact kernel equality from injectivity of the cokernel-to-tensor map.

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
