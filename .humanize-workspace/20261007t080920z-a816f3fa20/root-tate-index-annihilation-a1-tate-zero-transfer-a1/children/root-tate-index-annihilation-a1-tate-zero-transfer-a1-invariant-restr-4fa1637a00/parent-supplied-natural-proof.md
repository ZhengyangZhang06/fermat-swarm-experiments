# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1`
- Child DAG node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1.invariant_restriction_norm_range-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write B for A restricted to H, and N_L(v) = Σ(l ∈ L) l v for L = G or H. Left multiplication permutes L, so N_L(v) is L-invariant. Right multiplication permutes L, so N_L(l v − v) = 0. Hence N_L kills the span of these differences and induces ν_L on coinvariants. By the frozen definition, ν_L is normBar and ν_L([v]) is normToInvariants(v). Every coinvariant has a representative, so the image of ν_L consists exactly of these norm values.
2. Define j on G-invariants by retaining the underlying vector. Every element of H acts through an element of G, so that vector is H-invariant. Addition and scalar multiplication are inherited from A, making j k-linear, and its underlying vector is unchanged.
3. Choose a set S with exactly one representative of each right coset Hs. This is a finite set since G is finite. The map H × S → G sending (h,s) to hs is surjective by the definition of representatives. If hs = h′ s′, their right cosets agree, hence s = s′, and cancellation then gives h = h′. Thus this map is bijective. For v ∈ A put w = Σ(s ∈ S) s v. Linearity and this bijection give N_H(w) = Σ(h ∈ H)Σ(s ∈ S) hs v = N_G(v). These equalities hold as H-invariant elements after applying j to the ambient norm.
4. Let y belong to the range of ν_G. By step 1 choose v with y = ν_G([v]). Step 3 gives j(y) = ν_H([w]), so j(y) lies in the range of ν_H. This is precisely range(ν_G) ≤ comap(j, range(ν_H)), proving both required properties of j.

## Key steps

1. Identify normBar values with norms of coinvariant representatives.
2. Construct the linear inclusion of ambient invariants into subgroup invariants.
3. Use the right-coset multiplication bijection to express every ambient norm as a subgroup norm.
4. Deduce the required inclusion of norm ranges.

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
