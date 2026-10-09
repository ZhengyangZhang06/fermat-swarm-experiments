# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_index_annihilation-a1.homology_transfer-a1`
- Child DAG node: `root.tate_index_annihilation-a1.homology_transfer-a1.coinvariant_complex_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a commutative ring k, a finite group G, a k-linear G-representation A, a subgroup H with its given finite-type structure, a chain complex C of k-linear G-representations indexed by the natural numbers, and n. Write d=[G:H]. For each m let W_m=A⊗_k C_m, with diagonal G-action, and differential δ=id_A⊗∂_C. These differentials are G-equivariant and square to zero. In degree zero the outgoing differential is zero. Let D_G=(W_*)_G and D_H=(W_*)_H. By the definitions of restriction and coinvariantsTensorObj, these are exactly the two complexes appearing in the Lean statement: restricting a diagonal tensor representation gives the tensor product of the two restricted representations, with the same differentials.
2. Choose a finite right transversal S, one representative for each coset Hs. Inversion sends Hs to s⁻¹H and is a bijection between right and left cosets, so |S|=d. For any G-representation W, let q_H and q_G be the quotient maps by the k-spans of hw-w and gw-w respectively. Each H-relation is a G-relation. Thus there is a k-linear map π_W:W_H→W_G with π_W(q_H(w))=q_G(w).
3. Define the k-linear map F_W:W→W_H by F_W(w)=Σ_{s∈S}q_H(sw). If s is replaced by h s for h∈H then q_H(hsw)=q_H(sw), since their difference is an H-relation. Consequently this sum depends only on the right cosets of its representatives.
4. For g∈G, right multiplication sends Hs to Hsg bijectively, with inverse right multiplication by g⁻¹. Hence Sg is another right transversal. The representative independence from step 3, followed by reindexing the finite sum, gives F_W(gw)=Σ_s q_H(sgw)=F_W(w). Thus F_W kills every generator gw-w of the G-relation submodule, and by linearity it kills its k-span. It induces a k-linear map τ_W:W_G→W_H with τ_W(q_G(w))=F_W(w).
5. Compute π_Wτ_W(q_G(w))=Σ_s q_G(sw)=Σ_s q_G(w)=d•q_G(w), since each sw-w is a G-relation. Every element of W_G has a representative w. This proves π_Wτ_W=d•id, with the scalar action understood as repeated addition.
6. Apply these constructions to W_m using the same S in every degree. For each differential δ:W_m→W_j, equivariance gives δ(sw)=sδ(w). On representatives this implies δ_H τ_{W_m}=τ_{W_j}δ_G; linearity of δ justifies moving it through the finite sum. The equality δ_G π_{W_m}=π_{W_j}δ_H follows directly from the quotient formulas. Surjectivity of the quotient maps extends these identities to all classes. Thus τ:D_G→D_H and π:D_H→D_G are chain maps and πτ=d•id degreewise.
7. A chain map sends cycles to cycles because it commutes with the outgoing differential. It sends boundaries to boundaries because it commutes with the incoming differential. Consequently τ and π induce k-linear maps T:H_n(D_G)→H_n(D_H) and P:H_n(D_H)→H_n(D_G).
8. Represent any homology class x by a cycle z. The composite P(T(x)) is represented by πτ(z)=d•z, hence equals d•x. This also applies in degree zero, where every chain is an outgoing cycle. With the identifications in step 1, these T and P prove the exact statement.

## Key steps

1. Identify the two complexes as G- and H-coinvariants of the same diagonal tensor complex.
2. Choose a right transversal of cardinality equal to the subgroup index.
3. Construct the quotient projection and prove representative independence of the transfer sum.
4. Use right multiplication of right cosets to descend transfer through G-coinvariants.
5. Compute projection after transfer as the index times the identity.
6. Use equivariance of the differential to obtain chain maps.
7. Pass to cycles modulo boundaries and retain the index identity in every natural degree.

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
