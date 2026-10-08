# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1.unimodular_eigenrow_normalization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix R,k,r,s and choose x,y with xr+ys=1. First assume there is a unit u satisfying the two eigenrow equations. Write v for its value in R, so s=vr and ks−r=vs.
2. Set w=x+yv. Substituting s=vr into the unimodularity identity gives wr=(x+yv)r=xr+ys=1. Commutativity gives rw=1 as well, so r is a unit with inverse w.
3. Substitute s=vr into the second eigenrow equation. It becomes (kv−1)r=v²r. Multiplying by w and using rw=1 yields kv−1=v², equivalently v²−kv+1=0. Thus t=v satisfies s=rt and the required polynomial equation.
4. If t′ also satisfies s=rt′ and the polynomial equation, then rt′=s=rv. Multiplication by w gives t′=v. This proves the required unique existence, together with IsUnit r from step 2.
5. Conversely, assume r is a unit and there exists exactly one t satisfying s=rt and t²−kt+1=0. Choose that t. Its polynomial equation gives kt−t²=1, hence t(k−t)=1. Commutativity gives (k−t)t=1, so t is the value of a unit u whose inverse is k−t.
6. The equation s=rt becomes s=ur by commutativity. Moreover, ks−r=krt−r=r(kt−1)=rt²=t(rt)=us, where kt−1=t² follows from the polynomial equation. Thus this u satisfies both eigenrow equations. Together with steps 2–4, this proves the equivalence, including uniqueness, over every commutative ring.

## Key steps

1. Substitute s=ur into a unimodularity witness to construct an inverse of r.
2. Cancel the unit r in the second eigenrow equation to obtain t²−kt+1=0 with t=u.
3. Use invertibility of r to prove uniqueness of the normalized coordinate.
4. Conversely use the quadratic equation to construct the unit t with inverse k−t.
5. Substitute s=rt to recover both eigenrow equations.

## Reference use

### local-project

Queries:
- `nuTwo|nuThree|unimodularRow|ProjectiveLine|fixedPoints`
- `def Gamma0|mem_Gamma0|rightRel|quotientRightRelEquivQuotientLeftRel|eq_iff_div_mem|inv.*Quotient|Quotient.*inv`
- `isUnit_iff_exists|isUnit_iff.*mul|SL2_inv_expl|coe.*S|coe.*T`
- `nuTwo|nuThree|[Ff]ixed.*[Rr]oot|[Rr]oot.*[Ff]ixed|[Cc]oset.*[Uu]nimodular|[Uu]nimodular.*[Cc]oset`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_ProjectiveLine.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/GroupTheory/Coset/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`

The manifest pins project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. GenusNumerics defines nuTwo and nuThree as the stated root-subtype cardinalities. ProjectiveLine defines unimodular rows modulo common unit scaling. CongruenceSubgroups provides Gamma0_mem; Coset/Defs provides the left/right coset relations and their inversion equivalence; SpecialLinearGroup provides SL2_inv_expl and the concrete S and T matrices. No matching fixed-point-count theorem was found in the searched project Definitions and mathlib ModularForms files. The proposed interfaces use the imported coset and ring infrastructure directly.
