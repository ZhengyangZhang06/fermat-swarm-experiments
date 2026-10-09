# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_index_annihilation-a1.homology_transfer-a1`
- Child DAG node: `root.tate_index_annihilation-a1.homology_transfer-a1.restricted_standard_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a commutative ring k, a finite group G, a k-linear G-representation A, a subgroup H with a finite-type structure, and n. For L=G or H, write B(L) for Rep.standardComplex k L. Its degree-m module is the free k-module on tuples (g_0,…,g_m)∈L^{m+1}, with diagonal left L-action. Its differential in positive degree is the alternating sum of vertex deletions; its degree-zero outgoing differential is zero. These descriptions are precisely Rep.standardComplex.xIso and Rep.standardComplex.d_eq in the pinned Resolution.lean. Deletion is equivariant; for i<j the two orders of deleting those original vertices have signs (-1)^{i+j-1} and (-1)^{i+j}, so the differential squares to zero.
2. Choose one representative s for each right coset Hs, choosing 1 for H. Every g∈G has a unique expression hs: existence follows from membership in its represented coset; equality of two expressions first identifies the coset representatives and then identifies h by cancellation. Set r(hs)=h∈H, and let i:H→G be inclusion. Uniqueness implies r(hg)=h r(g) for h∈H, and the representative 1 implies r(i(h))=h.
3. Applying r or i to every vertex gives H-equivariant k-linear chain maps R:B(G)|_H→B(H) and I:B(H)→B(G)|_H, since vertexwise maps commute with every deletion. The equality r i=id_H gives R I=id on chains.
4. Put u=id_G and v=i r. For a tuple c=(g_0,…,g_m), define D_m(c)=Σ_{j=0}^m(-1)^j(ug_0,…,ug_j,vg_j,…,vg_m), and extend k-linearly. Each summand is H-equivariant, because u and v are H-equivariant. Set the formal degree-minus-one component to zero.
5. Expand ∂D_m+D_{m-1}∂ on c. In the j-th prism term, deleting position k<j cancels the term obtained by first deleting g_k and then using prism position j-1: their signs are (-1)^{j+k} and (-1)^{k+j-1}. Deleting position k>j+1 cancels first deleting g_{k-1} and using prism position j: their signs are (-1)^{j+k} and (-1)^{k-1+j}. Every D∂ term is in exactly one of these pairs: if the deleted original index is l and the prism index after deletion is t, use the first pairing when l≤t (j=t+1,k=l), and the second when l>t (j=t,k=l+1).
6. The remaining deletions are at k=j and k=j+1. They contribute respectively +(ug_0,…,ug_{j-1},vg_j,…,vg_m) and -(ug_0,…,ug_j,vg_{j+1},…,vg_m). The negative term at j cancels the positive term at j+1. The two endpoints are the all-v tuple and minus the all-u tuple. Hence ∂D+D∂=I R-id. For m=0 this reads ∂(ug_0,vg_0)=vg_0-ug_0 and D∂=0, so it holds there as well.
7. Tensor R,I,D with id_A and pass to H-coinvariants of the diagonal action. This is legitimate because all maps are H-equivariant and hence preserve the relation submodules; tensoring and quotienting preserve the displayed linear equalities. We obtain chain maps R_A:K→E and I_A:E→K, where K=(A⊗B(G))_H is exactly the complex on the left side of the statement and E=(Res_H A⊗B(H))_H. They satisfy R_A I_A=id and I_A R_A-id=∂D_A+D_A∂. For a cycle z the latter difference is ∂D_Az, a boundary. Thus their induced homology maps are inverse k-linear maps.
8. Identify E with the inhomogeneous chain complex of Res_H A. In degree m send [a⊗(h_0,…,h_m)]_H to the inhomogeneous generator with coefficient h_0⁻¹a at (h_0⁻¹h_1,…,h_{m-1}⁻¹h_m). This is linear in a and extends linearly in the free-module variable, so it respects tensor relations. Simultaneous translation by l∈H leaves the coefficient unchanged, since (lh_0)⁻¹(la)=h_0⁻¹a, and leaves each adjacent ratio unchanged. It therefore annihilates the coinvariant relation submodule and descends.
9. The inverse sends a[x_1,…,x_m] to [a⊗(1,x_1,x_1x_2,…,x_1⋯x_m)]_H and extends over finitely supported sums. Taking adjacent ratios of these cumulative products gives the original x_j, proving one composite is the identity. For the other composite, translating the original tensor by h_0⁻¹ normalizes its first vertex to 1, changes its coefficient to h_0⁻¹a, and gives exactly the cumulative-product tuple obtained from its adjacent ratios. Such simultaneous translation does not change its coinvariant class. This proves the other identity.
10. On the normalized tuple (1,x_1,x_1x_2,…,x_1⋯x_m), deleting the first vertex and normalizing gives (x_1⁻¹a)[x_2,…,x_m]. Deleting internal vertex i gives (-1)^i a[x_1,…,x_i x_{i+1},…,x_m], and deleting the last gives (-1)^m a[x_1,…,x_{m-1}]. These are all the faces. Their sum is exactly groupHomology.inhomogeneousChains.d_single from the pinned GroupHomology/Basic.lean, including its inverse action. The degree-zero outgoing boundaries are zero on both sides. Thus steps 8 and 9 give a k-linear chain isomorphism.
11. By definition groupHomology(Res_H A,n) is the homology of that inhomogeneous complex. Compose the linear homology equivalence induced by R_A from step 7 with the one from the chain isomorphism of step 10. Its inverse is the reverse composite of the respective inverses, so this is a k-linear equivalence from H_n(K) to groupHomology(Res_H A,n). It provides the witness to Nonempty in the exact Lean statement, including n=0.

## Key steps

1. Use the existing homogeneous standard complexes and their deletion differentials.
2. Choose a normalized right transversal and construct an H-equivariant retraction G→H.
3. Apply inclusion and retraction coordinatewise to obtain chain maps with one composite equal to the identity.
4. Construct the equivariant prism operator and verify every cancellation, including degree zero.
5. Tensor and pass to H-coinvariants, obtaining mutually inverse maps on homology.
6. Construct inverse homogeneous-to-inhomogeneous chain identifications.
7. Check the inverse-action boundary formula and compose the resulting homology equivalences.

## Reference use

### local-project

Queries:
- `standard|barComplex|homogeneous|def |abbrev |namespace`
- `def res|def.*coinvariants|coinvariantsFunctor|mapHomologicalComplex`
- `transfer|corestriction`
- `coinvariantsTransfer|coinvariantsCores|cosetDecomp_apply`
- `p04_ht_coinvariant_complex_transfer|p04_ht_restricted_standard_comparison`
- `homology.*ModuleCat|homologyIso|homologyπ.*surjective|quotient|Homology`
- `tprod|tensorObj|curriedTensor`
- `python3 /tmp/p04-ht-decomposition/run_audit.py TypeAudit`
- `python3 /tmp/p04-ht-decomposition/run_audit.py AssemblyAudit`
- `python3 /tmp/p04-ht-decomposition/run_audit.py InstanceAudit`
- `python3 /tmp/p04-ht-decomposition/run_audit.py deps`
- `python3 /tmp/p04-ht-decomposition/run_audit.py submission`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions/Def_GroupCohomology_TateCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/Resolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupHomology/Functoriality.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Coinvariants.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean`
- `/tmp/p04-ht-decomposition/contracts.json`
- `/tmp/p04-ht-decomposition/TypeAudit.lean`
- `/tmp/p04-ht-decomposition/TypeAudit.log`
- `/tmp/p04-ht-decomposition/AssemblyAudit.lean`
- `/tmp/p04-ht-decomposition/AssemblyAudit.log`
- `/tmp/p04-ht-decomposition/InstanceAudit.lean`
- `/tmp/p04-ht-decomposition/InstanceAudit.log`
- `/tmp/p04-ht-decomposition/DependencyAudit.json`
- `/tmp/p04-ht-decomposition/SubmissionImportAudit.log`

The snapshot revisions match the manifest: project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Both snapshot trees and all nine pinned installed dependencies are clean. Resolution.lean supplies the homogeneous standard complex, its deletion differential, and standardResolution. GroupHomology/Basic.lean supplies the inverse-action inhomogeneous differential and groupHomologyIso, so the parent needs no additional named comparison theorem for G itself. Coinvariants.lean supplies quotient, lift, and tensor-coinvariant infrastructure; the transfer/corestriction search there and in Resolution.lean returned no matches. GroupHomology/Functoriality.lean contains corestriction infrastructure. Neither proposed identifier occurs in the inspected project declarations or active DAG. Both exact child propositions elaborate with import Mathlib under Lean 4.33.1; a conditional Lean assembly proof establishes the exact parent contract from them. Instance checks verify diagonal tensor action, compatibility with restriction, and the additive natural-number action on homology. Audited library declarations depend only on propext, Classical.choice, and Quot.sound. However, the mandatory import Submission gate remains blocked: compiling unchanged Submission.lean fails at line 10 on the missing constant Representation.TateResCor.cosetDecomp_apply. Thus these are checked mathematical proposals, not activation-ready child contracts or comparator-accepted proofs. No frozen source was changed.
