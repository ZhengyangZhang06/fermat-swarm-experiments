# Parent-supplied natural-language proof

- Parent DAG node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1`
- Child DAG node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1.inverse_coset_row_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N≠0 and A,B∈SL₂(ℤ). Work in the commutative ring R=ℤ/Nℤ when discussing matrix entries. Write the bottom rows of A and B as (c,d) and (c′,d′), respectively, and put H=Γ₀(N).
2. For any subgroup H, equality gH=hH is equivalent to g⁻¹h∈H: membership expresses h as gh₀ for h₀∈H, and conversely equal cosets imply h∈gH. Applying this to g=A⁻¹ and h=B⁻¹ shows that A⁻¹H=B⁻¹H is equivalent to AB⁻¹∈H. Since a subgroup is closed under inversion, this is also equivalent to E=BA⁻¹ belonging to H.
3. Suppose the cosets are equal. By step 2, E∈H, so its reduced matrix has the form ((a,b),(0,e)). Reduction preserves the determinant, and det E=1, hence ae=1 in R. Commutativity also gives ea=1. Thus e is the value of a unit u with inverse a.
4. The identity B=EA follows from E=BA⁻¹. Multiplying the bottom row (0,e) of E by A gives c′=ec and d′=ed. The unit u from step 3 therefore satisfies both required scaling equations.
5. Conversely, suppose there is a unit u with c′=uc and d′=ud. Since det A=1, if A=((a,b),(c,d)), then A⁻¹=((d,−b),(−c,a)). Consequently the reduced bottom-left entry of E=BA⁻¹ is c′d−d′c. Substituting the scaling equations gives ucd−udc=0 by commutativity. Hence E∈Γ₀(N).
6. Step 2 now gives A⁻¹H=B⁻¹H. This proves both implications. Every calculation remains valid in ℤ/1ℤ, so no additional restriction on N is needed.

## Key steps

1. Translate equality of inverse left cosets into BA⁻¹∈Γ₀(N).
2. Use determinant one to show the bottom-right entry of an upper-triangular reduction is a unit.
3. Multiply B=(BA⁻¹)A to obtain common unit scaling of bottom rows.
4. Conversely compute (BA⁻¹)₁₀=c′d−d′c and use scaling to make it zero.
5. Recover the required coset equality from subgroup membership.

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
