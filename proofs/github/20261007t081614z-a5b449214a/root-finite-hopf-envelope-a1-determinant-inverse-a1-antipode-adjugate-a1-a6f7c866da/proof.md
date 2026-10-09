# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_hopf_envelope-a1.determinant_inverse-a1`
- Child DAG node: `root.finite_hopf_envelope-a1.determinant_inverse-a1.antipode_adjugate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k,H,n,c satisfying the hypotheses. Define the ordinary matrix Q by Q_ij=S(c_ij). Write m:H⊗_k H→H for the k-linear multiplication map. Apply m∘(S⊗id) to Δ(c_ij)=Σ_l c_il⊗c_lj. Linearity and the left antipode identity give Σ_l S(c_il)c_lj=algebraMap(ε(c_ij))=δ_ij in H. These are exactly the entries of Qc=I. Applying m∘(id⊗S) instead gives Σ_l c_ilS(c_lj)=δ_ij, hence cQ=I. Here I denotes the ordinary identity matrix.
2. Put d=det(c) and u=det(Q). The commutative-ring identities Matrix.det_mul and Matrix.det_one, supplied by the pinned Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean, applied to cQ=I give du=det(cQ)=det(I)=1. Commutativity of H also gives ud=1.
3. Define the ordinary matrix T by T_ij=u adj(c)_ij. The identity Matrix.mul_adjugate in the pinned Mathlib/LinearAlgebra/Matrix/Adjugate.lean gives c adj(c)=dI. For every i,j, commutativity and distributivity therefore give (cT)_ij=Σ_l c_il(u adj(c)_lj)=u Σ_l c_il adj(c)_lj=u(dI_ij)=(ud)I_ij=I_ij. Consequently cT=I.
4. Associativity of ordinary matrix multiplication and Qc=I imply Q=QI=Q(cT)=(Qc)T=IT=T. Taking the i,j entry yields S(c_ij)=u adj(c)_ij. Together with du=1, this proves the required existential statement with u=det(Q).
5. No step requires n to be positive. When n=0, both determinants are 1 by Matrix.det_isEmpty, and the entrywise assertion has no indices, so the same argument covers the empty matrix.

## Key steps

1. Apply the two antipode identities to the coefficient comultiplication formulas to obtain Qc=I=cQ.
2. Set u=det(Q) and take determinants to obtain det(c)u=1.
3. Use c adj(c)=det(c)I to show that u adj(c) is a right inverse of c.
4. Compare this right inverse with Q using Qc=I and take entries.
5. Use the empty determinant convention to include n=0.

## Reference use

### local-project

Queries:
- `antipode_mul|antipodeAlgHom|antipode.*[Aa]lg|det_mul|det_map|mul_adjugate|adjugate_mul|hopfKer_eq_of_surjective`
- `antipodeAlgHom|antipode_mul|map_det|comulAlgHom|counitAlgHom|of_mul_eq_one`
- `(det.*(comul|[Gg]roup[Ll]ike)|([Gg]roup[Ll]ike|comul).*det|antipode.*adjugate|adjugate.*antipode)`
- `p05_di_antipode_adjugate_a5b449214a|p05_di_determinant_grouplike_a5b449214a`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p05_di_typecheck_a5b449214a.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean HeaderPolicyCheck.lean`
- `python3 /tmp/p05_di_audit_a5b449214a.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/GroupLike.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Bialgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge/HeaderPolicyCheck.lean`
- `/tmp/p05_di_typecheck_a5b449214a.lean`
- `/tmp/p05_di_audit_a5b449214a.json`

The snapshots match project 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; both snapshots and all nine diagnostic compiler dependencies are clean and pinned. HopfAlgebra.Basic supplies both antipode identities; Convolution supplies antipodeAlgHom. The matrix files supply det_mul, RingHom.map_det, det_one, det_isEmpty, mul_adjugate and adjugate_mul. The targeted search found no existing determinant/comultiplication or antipode/adjugate theorem in the searched snapshot directories. Both proposed names were absent from the searched DAG, handoffs, snapshot and imported environment. Both exact child types elaborated after import Submission under Lean 4.33.1; kernel-checked diagnostic equalities confirmed ordinary multiplication for Matrix.of constructions. Audited library declarations have only propext, Classical.choice and Quot.sound as transitive axioms. Reviewed compiler-copy evidence matches policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: exactly authorized lines 10–11 were omitted, original hash 2e81f3c63685285e1af52e3dee0c135a8a7c8e9f37be7ad076712f55790c632c reversibly yields build hash d10948155ea0e92408d3ce320bdd5db3b7f00b622f4c9de9c98f040a414fa2f6, and the rerun Lean probe confirmed all omitted targets absent. These checks establish decomposition compatibility, not comparator acceptance of child proofs.
