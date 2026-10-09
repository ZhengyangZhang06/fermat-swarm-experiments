# Parent-supplied natural-language proof

- Parent DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1`
- Child DAG node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_exists-a1.coset_sum_equivariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data, g ∈ G, and x ∈ B. Write Q = G/H and t_q = Quotient.out q. For t ∈ G and y ∈ B, define L_t(y) = ρ_A(t)F(ρ_B(t⁻¹)y). Each sum below is finite because Q has the supplied Fintype structure.
2. Define T_g : Q → Q by T_g(tH) = (gt)H. This is well-defined: if sH = tH, then s⁻¹t ∈ H, and (gs)⁻¹(gt) = s⁻¹t ∈ H, so (gs)H = (gt)H. The map T_{g⁻¹} is an inverse, since g⁻¹(gt) = t and g(g⁻¹t) = t. Consequently T_g is a permutation of Q.
3. The element t_{T_g(q)} represents T_g(q), and gt_q also represents T_g(q). Apply coset_summand_independence to these two group elements and the vector ρ_B(g)x. It gives L_{t_{T_g(q)}}(ρ_B(g)x) = L_{gt_q}(ρ_B(g)x) for each q ∈ Q.
4. Since (gt_q)⁻¹ = t_q⁻¹g⁻¹, the representation laws give L_{gt_q}(ρ_B(g)x) = ρ_A(g)ρ_A(t_q)F(ρ_B(t_q⁻¹)ρ_B(g⁻¹)ρ_B(g)x). The identity ρ_B(g⁻¹)ρ_B(g) = id reduces this to ρ_A(g)L_{t_q}(x).
5. Reindexing a finite sum by the permutation T_g does not change it: each index appears exactly once. Hence Σ_q L_{t_q}(ρ_B(g)x) = Σ_q L_{t_{T_g(q)}}(ρ_B(g)x). Substitute steps 3 and 4 to obtain Σ_q L_{t_q}(ρ_B(g)x) = Σ_q ρ_A(g)L_{t_q}(x).
6. The action map ρ_A(g) is k-linear and therefore additive, so it preserves this finite sum. The last expression equals ρ_A(g)(Σ_q L_{t_q}(x)). Expanding L_t gives exactly the asserted equality.

## Key steps

1. Define the summand L_t and the finite left-coset index set.
2. Prove left multiplication by g permutes the cosets, with inverse multiplication by g⁻¹.
3. Use representative independence to replace t_{T_g(q)} by gt_q.
4. Expand the representation laws and cancel the inverse actions on B.
5. Reindex the finite sum by T_g.
6. Move the additive map ρ_A(g) outside the sum.

## Reference use

### local-project

Queries:
- `coset.*[Aa]verag|[Aa]verag.*coset|[Hh]om.*[Tt]ransfer|[Tt]ransfer.*[Hh]om`
- `def res|res_ρ|res_hom|resFunctor`
- `def res|def ρ|abbrev ρ|structure Hom|def mkHom|comm_apply|hom_apply|def hom`
- `smul_mk|smul_out|mul_left|smul.*out|MulAction`
- `theorem sum_comp|lemma sum_comp|sum_equiv|sum_bijective`
- `p04_hca_bc7c754a4b_summand_eq_of_coset_eq|p04_hca_bc7c754a4b_sum_equivariant`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain --untracked-files=no`
- `command -v lean lake elan python3`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Coset/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/Submission.lean`

The manifest pins project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib has that HEAD and no tracked modifications; inspected Rep/Basic, Rep/Res, and Coset/Defs and Basic files match the snapshot byte for byte. Rep.hom_comm_apply supplies equivariance, and restriction preserves underlying vector spaces. QuotientGroup.eq characterizes equality of left cosets by s⁻¹t ∈ H; the quotient-action API supplies left multiplication and representative identities without normality. Finite-sum reindexing is available. The targeted averaging search found no relevant match, and neither proposed identifier occurs in the inspected DAG, node contracts, or Submission source. No Lean executable or compiled Submission was available, so elaboration and transitive axiom checks were not performed; these source checks do not constitute comparator acceptance.
