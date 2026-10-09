# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_parabolic-a1.integral_parabolic_normal_form-a1`
- Child DAG node: `root.primitive_parabolic-a1.integral_parabolic_normal_form-a1.primitive_kernel-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix an integral 2×2 matrix M with determinant zero. If M=0, take p=1 and q=0. The coefficients 1 and 0 give 1p+0q=1, so IsCoprime p q, and M(p,q)=0.
2. Suppose M≠0 and write M=(a b;c d). If (a,b)≠(0,0), choose (x,y)=(b,−a). This vector is nonzero, and its image is (ab−ba,cb−da)=(0,−det M)=(0,0). If (a,b)=(0,0), then (c,d)≠(0,0); choose (x,y)=(d,−c). It is nonzero and its image is (0,cd−dc)=(0,0). Thus M(x,y)=0 with x and y not both zero.
3. Let g=gcd(|x|,|y|), regarded as an integer. Since x,y are not both zero, g>0. It divides both x and y, so there are integers p,q with x=gp and y=gq. Bézout's identity supplies integers α,β with αx+βy=g.
4. Substitute x=gp and y=gq into that identity to obtain g(αp+βq)=g. Since g≠0 and ℤ is an integral domain, cancellation gives αp+βq=1. These α,β witness IsCoprime p q.
5. The two coordinates of M(x,y)=0 become g(ap+bq)=0 and g(cp+dq)=0. Cancel g≠0 in both equations. The resulting equations say exactly M.mulVec ![p,q]=0, proving the conclusion.

## Key steps

1. Handle the zero matrix using the primitive vector (1,0).
2. For a nonzero singular matrix, construct a nonzero kernel vector perpendicular to a nonzero row.
3. Divide its coordinates by their positive gcd.
4. Cancel the gcd in Bézout's identity to establish IsCoprime.
5. Cancel the gcd in both kernel equations.

## Reference use

### local-project

Queries:
- `parabolic|trace.*(4|2)|trace_sq|IsCoprime|gcdA|zpow.*T|eichlerShimuraMap_injective`
- `parabolic.*conjug|conjug.*parabolic|trace.*(sq|\^ 2)|primitive.*(ker|eigen)|exists.*(ker|coprime)`
- `coe_T_zpow|T_zpow|def T|theorem coe_mul|theorem coe_neg|mkOf`
- `det_fin_two|mulVec_fin_two|mulVec_smul|mulVec_mulVec|def IsCoprime`
- `p02_es_177ebb5a_pnf_(primitive_kernel|primitive_eigenvector_triangular)`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_177ebb5a_pnf_decomposition.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_Gamma0CoeffCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Int/GCD.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/Coprime/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/Coprime/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Data/Matrix/Mul.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/Submission.lean`
- `/tmp/p02_177ebb5a_pnf_decomposition.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib has that revision and clean Git status; the five compared supporting mathlib files and Def_Gamma0CoeffCohomology.lean match the snapshot byte-for-byte. The snapshot supplies Int.gcd_eq_gcd_ab, Int.exists_gcd_one, Int.isCoprime_iff_gcd_eq_one, Matrix.det_fin_two, matrix-vector identities, and ModularGroup.coe_T_zpow. No matching integral conjugacy theorem was found in the searched project and matrix/modular-form sources. Both proposed names have no matches in Submission or the current DAG metadata. Both exact child types elaborate after import Submission. Additional checked examples verify special-linear multiplication and negation, the constructed matrix determinant, and matrix-vector multiplication. Transitive axiom checks on eleven supporting declarations report only propext, Classical.choice, and Quot.sound. These establish interface compatibility and reference suitability, not comparator acceptance of new proofs.
