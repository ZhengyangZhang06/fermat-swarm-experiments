# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.subalgebra_coinvariant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write ε for the counit of H. For t∈K put u=t−algebraMap(k,H)(ε(t)). The subalgebra contains scalar images and is closed under subtraction, so u∈K. Since ε is a k-algebra homomorphism, ε(u)=ε(t)−ε(t)=0.
2. Thus u belongs to the generating set of the ideal in hker, hence to ker(q). Preservation of scalar images by q gives q(t)=algebraMap(k,B)(ε(t)) for every t∈K.
3. For x∈K, hΔ expresses Δ_H(x) as a finite k-linear combination of pure tensors with both factors in K. Absorbing each scalar coefficient into its first factor gives Δ_H(x)=Σ_i a_i⊗b_i with a_i,b_i∈K.
4. Apply id_H⊗q and use step 2. The result is Σ_i a_i⊗algebraMap(k,B)(ε(b_i))=(Σ_i ε(b_i)a_i)⊗1_B. The right counit identity applied to the expression in step 3 gives Σ_i ε(b_i)a_i=x. Therefore (id_H⊗q)Δ_H(x)=x⊗1_B.
5. This is exactly the defining membership equation of HopfAlgebra.hopfKer q. It holds for every x∈K, proving K≤HopfAlgebra.hopfKer q.

## Key steps

1. Subtract the counit scalar to obtain an augmentation generator in K.
2. Use the kernel equality to determine q on K.
3. Expand comultiplication with both tensor factors in K.
4. Use the right counit identity to obtain coinvariance.
5. Translate coinvariance into Hopf-kernel membership.

## Reference use

### local-project

Queries:
- `HopfKerHopf|ι₂_comulK|def coaction|def hopfKer|mem_hopfKer`
- `antipode_mul_distrib|antipodeAlgHom|isNoetherianRing_of_fg|finitePresentation_of_finite|one_tmul_eq_zero_iff|eqLocus_includeLeft_includeRight|of_faithfullyFlat`
- `p05_finite_hopf_envelope_a5b449214a|p05_finite_retraction_a5b449214a|p05_hopf_tensor_equalizer_a5b449214a|p05_subalgebra_coinvariant_a5b449214a|p05_canonical_map_injective_a5b449214a`
- `rg --files -uu -g dag.json /mnt/data/zhengyang-workspace/fermat-swarm-projects`
- `rg --files /runtime -g 'policy.json' -g '*header*policy*' -g '*authorization*' -g '*repair*receipt*' -g '*repair*report*'`
- `python3 .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/validate.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Fermat/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Adjoin/FG.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/TensorProduct/IncludeLeftSubRight.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/runtime/flows/math-lean-flow-header-policy-v4/docs/frozen-header-policy.md`
- `/runtime/flows/math-lean-flow-header-policy-v4/scripts/verify-frozen-node.py`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/header-input-binding.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge/CheckInstances.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge/InfrastructureAxioms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge-header-absence.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge-infrastructure-axioms.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/solution-infrastructure-axioms.log`

The pinned definition identifies Hopf-kernel membership with coaction(q,x)=x⊗1. The inspected library provides antipode multiplicativity and Noetherian finite-presentation infrastructure; its generic tensor equalizer and zero-detection results require effectiveness or faithful flatness, which these proofs establish directly instead of assuming. Searches found neither the orphan HopfKerHopf declarations nor the proposed helper names in the pinned Definitions/mathlib trees; no competing local DAG reservations were found. The project and mathlib snapshots are clean at 2fdd42759f4ab17640ac773289b521dd69d4b26e and db584cd6d46c92f209a44c0f1c829460d327499d, and all nine dependency checkouts match their clean pins. A newly published controller policy with SHA-256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 authorizes omitting only frozen lines 10–11 in shared derived compiler copies. Fresh validation replayed the controller preparation functions, checked reversible source hashes, built both Submission contexts and the independent Challenge, and passed all five unchanged literal propositions after import Submission, inclusion/scalar/tensor probes, the 13-name absence probe, and nine transitive infrastructure axiom checks in both contexts. Only propext, Classical.choice and Quot.sound occur in those infrastructure closures. No child type constructs a matrix. Original frozen files and dependencies remain unchanged. These are decomposition-context checks, not acceptance of the still-unproved root or any child proof.
