# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_hopf_envelope-a1.determinant_inverse-a1`
- Child DAG node: `root.finite_hopf_envelope-a1.determinant_inverse-a1.determinant_grouplike-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k,H,n,c satisfying the hypotheses and put d=det(c). The bialgebra axioms make Δ:H→H⊗_k H and ε:H→k unital k-algebra homomorphisms, represented by Bialgebra.comulAlgHom and Bialgebra.counitAlgHom. The tensor product is a commutative k-algebra. Its two inclusions λ(a)=a⊗1 and ρ(a)=1⊗a are also unital k-algebra homomorphisms.
2. Define ordinary matrices X and Y over H⊗_k H by X_ij=λ(c_ij) and Y_ij=ρ(c_ij). For every i,j, ordinary matrix multiplication and tensor multiplication give (XY)_ij=Σ_l (c_il⊗1)(1⊗c_lj)=Σ_l c_il⊗c_lj=Δ(c_ij). Thus applying Δ entrywise to c produces XY.
3. Use determinant functoriality RingHom.map_det and multiplicativity Matrix.det_mul from the pinned Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean. Step 2 gives Δ(d)=det(XY)=det(X)det(Y). Since X and Y are obtained by applying λ and ρ entrywise, functoriality also gives det(X)=λ(d)=d⊗1 and det(Y)=ρ(d)=1⊗d. Therefore Δ(d)=(d⊗1)(1⊗d)=d⊗d.
4. The counit hypothesis says that applying ε entrywise to c yields the ordinary identity matrix over k. Determinant functoriality and Matrix.det_one therefore give ε(d)=det(ε(c))=det(I)=1. This establishes both asserted identities.
5. These determinant identities require no nonempty index set. When n=0, d=1 by Matrix.det_isEmpty, and the conclusions also follow directly from preservation of the unit by Δ and ε.

## Key steps

1. Use the algebra homomorphisms Δ, ε and the two tensor inclusions.
2. Factor the entrywise comultiplication matrix as the product of the two inclusion matrices.
3. Apply determinant functoriality and multiplicativity to obtain Δ(det(c))=det(c)⊗det(c).
4. Apply determinant functoriality to the counit identity matrix to obtain ε(det(c))=1.
5. Include n=0 through the empty determinant convention.

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
