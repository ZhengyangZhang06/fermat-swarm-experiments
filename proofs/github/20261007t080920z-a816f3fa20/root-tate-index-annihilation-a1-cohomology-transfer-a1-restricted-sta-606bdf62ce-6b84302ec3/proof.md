# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1`
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.noncentral_cancellation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data, put N=n+1, and write x_i=c(i). Identify finite indices with their natural-number values. By the insertion definition, Q_m(d,j) has entry u(d_r) at positions r≤j and v(d_{r−1}) at positions r>j. Deleting position a replaces the argument r by r when r<a and by r+1 when r≥a.
2. Consider a first-sum index with a<j. Set b=a and t=j−1. Since 1≤j≤N, we have 0≤t≤N−1 and 0≤b≤N. Put d=c ∘ b.succAbove, so d_r=x_r for r<a and d_r=x_{r+1} for r≥a. At output positions s≤t, deleting position a from Q_N(c,j) gives u(x_s) for s<a and u(x_{s+1}) for s≥a; these are u(d_s). At positions s>t, we have s≥j>a, and the deleted tuple has entry v(x_s)=v(d_{s−1}). Thus Q_N(c,j) ∘ a.succAbove = Q_{N−1}(d,t).
3. Consider instead a first-sum index with a>j+1. Set b=a−1 and t=j. The bounds a≤N+1 and a≥j+2 imply 0≤t≤N−1 and 0≤b≤N. Put d=c ∘ b.succAbove. At positions s≤j, the deleted tuple has entry u(x_s)=u(d_s), because s<a−1. At positions j<s<a it has entry v(x_{s−1})=v(d_{s−1}); at positions s≥a it has entry v(x_s)=v(d_{s−1}). These cases exhaust all output positions, proving Q_N(c,j) ∘ a.succAbove = Q_{N−1}(d,t).
4. These assignments give a bijection with all second-sum indices (b,t). Explicitly, if b≤t, take j=t+1 and a=b. Then j≤N, a<j, and the assignment in step 2 returns (b,t). If b>t, take j=t and a=b+1. Then a≤N+1, a>j+1, and step 3 returns (b,t). Conversely, the first case produces b≤t, the second produces b>t, and these inverse formulas recover the original (j,a). The two cases are disjoint and exhaustive.
5. In both cases j+a=b+t+1. Hence (−1)^(j+a)=−(−1)^(b+t) in k. Steps 2 and 3 identify the corresponding tuples. Additivity of MonoidAlgebra.single in its coefficient therefore makes each paired sum equal to S(d,−r)+S(d,r)=S(d,0)=0, where r=(−1)^(b+t).
6. Reindex the filtered first double sum using the bijection of step 4 and combine it with the second double sum. Finite-sum distributivity and step 5 make every summand zero. This proves the asserted equality. The bijection is between indices, so repeated tuples and noninjective u or v do not affect the argument.

## Key steps

1. Evaluate the inserted prism tuple coordinatewise.
2. Identify deletion before the transition with the smaller prism having transition j−1.
3. Identify deletion after the transition with the smaller prism having transition j.
4. Construct the inverse pairing using the exhaustive cases b≤t and b>t.
5. Show paired coefficient exponents differ by one.
6. Reindex the finite sums and cancel every paired term.

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
