# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1`
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.central_telescoping-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data and write x_i=c(i). For every natural number ℓ with 0≤ℓ≤m+1, define T_ℓ : Fin(m+1) → X by T_ℓ(i)=u(x_i) when i.val<ℓ and T_ℓ(i)=v(x_i) otherwise. By the insertion definition, Q_j has entry u(x_r) at positions r≤j and v(x_{r−1}) at positions r>j, interpreting indices by their natural-number values.
2. Deleting position j from Q_j gives T_j. Indeed, at output positions i<j the retained position is i and its entry is u(x_i); at positions i≥j the retained position is i+1 and its entry is v(x_i). The deletion map here is j.castSucc.succAbove, so Q_j ∘ j.castSucc.succAbove=T_j as functions.
3. Deleting position j+1 from Q_j gives T_{j+1}. At output positions i≤j the retained position is i and its entry is u(x_i); at positions i>j the retained position is i+1 and its entry is v(x_i). This deletion map is j.succ.succAbove, giving Q_j ∘ j.succ.succAbove=T_{j+1}.
4. Substitute steps 2 and 3 into the stated sum. It becomes Σ_{j=0}^m ([T_j]−[T_{j+1}]). For each 1≤ℓ≤m, the term [T_ℓ] occurs positively at j=ℓ and negatively at j=ℓ−1. Associativity and commutativity of addition cancel all these interior terms, leaving [T_0]−[T_{m+1}]. When m=0 there are no interior terms, and the same equality holds directly.
5. Every i : Fin(m+1) satisfies 0≤i.val<m+1. Therefore T_0(i)=v(c(i)) and T_{m+1}(i)=u(c(i)) for all i. Thus T_0=v ∘ c and T_{m+1}=u ∘ c. Substituting these endpoint identities proves the required equality.

## Key steps

1. Define mixed tuples T_ℓ with a single transition at ℓ.
2. Identify deletion of position j with T_j.
3. Identify deletion of position j+1 with T_{j+1}.
4. Cancel the interior terms of the telescoping sum.
5. Identify the two endpoint tuples with v ∘ c and u ∘ c.

## Reference use

### local-project

Queries:
- `namespace standardComplex|standardComplex.d`
- `removeNth_insertNth|insertNth_apply_same|insertNth_apply_succAbove|insertNth_apply_below|insertNth_apply_above`
- `prism|prism_boundary|prismBoundary`
- `cosetDecomp_apply`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions/Def_GroupCohomology_TateCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/Resolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`

The manifest pins project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Resolution.lean defines the differential for arbitrary types and supplies d_of and d_single. Tuple/Basic.lean supplies insertion evaluation and insertNth_comp_succAbove. No prism identity was found in the searched project definitions, representation theory, or algebraic topology directories. All nine installed dependencies match their pins and have clean tracked sources. Both proposed expressions elaborate with Lean 4.33.1 against the unchanged frozen imports; the inspected library lemmas depend only on propext, Classical.choice, and Quot.sound. Neither proposed name is reserved in the current DAG. However, compiling unchanged Submission.lean fails at line 10 on the absent Representation.TateResCor.cosetDecomp_apply. Thus the required import Submission gate remains blocked; these checks do not authorize child activation or establish comparator acceptance.
