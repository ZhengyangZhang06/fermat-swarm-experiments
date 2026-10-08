# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1`
- Child DAG node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1.invariant_transfer_norm_index-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let Q be the finite set of left cosets G/H. Choose t(q) ∈ G representing each q ∈ Q. Its cardinality is d = H.index by the definition of index. The map Q × H → G, (q,h) ↦ t(q)h, is surjective because t(q) represents q. Equality t(q)h = t(q′)h′ first implies q = q′ by taking left cosets, and then h = h′ by cancellation; hence it is bijective.
2. For b ∈ A^H define c₀(b) = Σ(q ∈ Q) t(q)b in A. If t′(q) is another representative, t′(q) = t(q)h for an h ∈ H, and t′(q)b = t(q)b because b is H-invariant. Thus each summand depends only on its coset.
3. For g ∈ G, q ↦ gq is a permutation of Q with inverse q ↦ g⁻¹q. The element gt(q) represents gq, so step 2 gives gt(q)b = t(gq)b. Therefore g c₀(b) = Σ(q ∈ Q) gt(q)b = Σ(q ∈ Q) t(gq)b = c₀(b). Thus c₀(b) is G-invariant. Let c(b) be this vector equipped with that invariance proof.
4. Every action map t(q) is k-linear. Finite summation gives c₀(b+b′) = c₀(b)+c₀(b′) and c₀(r b) = r c₀(b). Equality in the invariant subtype is equality of underlying vectors, so c is a k-linear map A^H → A^G.
5. For L = H or G and v ∈ A, N_L(v) = Σ(l ∈ L) l v is invariant because left multiplication permutes L, and normToInvariants(v) is exactly this invariant element. Applying step 1 and the action law gives c₀(N_H(v)) = Σ(q ∈ Q)Σ(h ∈ H) t(q)h v = Σ(g ∈ G) g v = N_G(v). Equality of underlying vectors proves c(normToInvariants_H(v)) = normToInvariants_G(v).
6. Let a ∈ A^G and b ∈ A^H have equal underlying vectors. Every t(q) fixes a, so c₀(b) = Σ(q ∈ Q) a = |Q| • a = H.index • a in A, where • is repeated addition. The natural-number action on A^G is inherited from A. Equality of underlying vectors therefore yields c(b) = H.index • a in A^G. This establishes the second property of the same map c.

## Key steps

1. Choose left-coset representatives and prove the multiplication bijection.
2. Define the coset sum and establish independence of representatives.
3. Reindex by left multiplication to prove ambient invariance.
4. Establish linearity of the invariant-valued transfer.
5. Compute transfer of a subgroup norm as the ambient norm.
6. Evaluate on ambient invariant vectors to obtain repeated addition by the index.

## Reference use

### local-project

Queries:
- `tateH0|normBar|cosetNormInvariants|tateH0Res|tateH0Cores`
- `norm|invariants|res|mk_surjective`
- `p04_tz91_|TateResCor|tateH0Res|tateH0Cores`
- `lean_name|depth|candidate_commit|proof_base_commit`
- `def mapQ|theorem mapQ_apply|lemma mapQ_apply|mapQ_mkQ|mapQ_comp|mkQ_apply|mkQ_surjective`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions/Def_GroupCohomology_TateCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Coinvariants.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Coset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Index.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`
- `/tmp/p04-tz91-dependency-audit.json`
- `/tmp/p04-tz91-decomposition-6yojlzlg/contracts.json`
- `/tmp/p04-tz91-decomposition-6yojlzlg/TypeAudit.lean`
- `/tmp/p04-tz91-decomposition-6yojlzlg/TypeAudit.log`
- `/tmp/p04-tz91-decomposition-6yojlzlg/AssemblyAudit.lean`
- `/tmp/p04-tz91-decomposition-6yojlzlg/AssemblyAudit.log`
- `/tmp/p04-tz91-decomposition-6yojlzlg/Submission.log`

The snapshot confirms the normBar quotient definition, surjectivity of the coinvariant projection, the unchanged underlying module under restriction, coset decomposition, and Submodule.mapQ. No degree-zero subgroup transfer implementation or proposed-name collision was found in the searched definitions and DAG. Snapshot revisions match the manifest; all nine installed dependencies match their pinned revisions and have clean source trees. Both proposed types elaborate against unchanged frozen definitions with Lean 4.33.1. Instance checks confirm inherited repeated addition, and a warning-free conditional assembly proves the parent from the two contracts. Audited infrastructure has only propext, Classical.choice, and Quot.sound as transitive axioms. However, the required import Submission gate remains blocked: unchanged Submission.lean fails at line 10 on the unknown constant Representation.TateResCor.cosetDecomp_apply. These checks do not establish comparator acceptance or authorize child activation.
