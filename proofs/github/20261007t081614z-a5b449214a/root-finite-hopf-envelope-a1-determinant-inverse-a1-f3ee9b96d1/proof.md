# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_hopf_envelope-a1`
- Child DAG node: `root.finite_hopf_envelope-a1.determinant_inverse-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. First recall why S is a k-algebra homomorphism in this commutative setting. It is k-linear by the Hopf structure, and the antipode identity at 1 gives S(1)=1. For linear maps H⊗H→H, define convolution by (f*g)(a⊗b)=Σ f(a₁⊗b₁)g(a₂⊗b₂). Coassociativity and associativity show that both parenthesizations of a triple convolution have the same iterated sum. Counitality gives the convolution identity e(a⊗b)=ε(a)ε(b)1. The bilinear prescriptions f(a⊗b)=ab, g(a⊗b)=S(ab), and h(a⊗b)=S(a)S(b) define linear maps. Multiplicativity of Δ and ε and the antipode identity give (g*f)(a⊗b)=Σ S(a₁b₁)a₂b₂=ε(a)ε(b)1. Commutativity and the two individual antipode identities give (f*h)(a⊗b)=(Σ a₁S(a₂))(Σ b₁S(b₂))=ε(a)ε(b)1. Pure tensors span, so g*f=e=f*h. Hence g=g*(f*h)=(g*f)*h=h. Thus S(ab)=S(a)S(b); linearity and S(1)=1 also give preservation of k-scalars.
2. Let Q be the ordinary matrix whose entry Q_ij is S(c_ij). Apply multiplication after S on the first tensor factor to the assumed formula for Δ(c_ij). The antipode identity and the counit hypothesis give Σ_l S(c_il)c_lj=δ_ij in H. Applying S on the second factor instead gives Σ_l c_ilS(c_lj)=δ_ij. These are precisely Qc=I and cQ=I for ordinary matrix multiplication.
3. We use determinant identities valid over every commutative ring: det(XY)=det(X)det(Y), determinants commute with unital ring homomorphisms, and c adj(c)=adj(c)c=det(c)I. These are supplied by the pinned determinant and adjugate library. Their algebraic justification uses the permutation formula: homomorphisms preserve its sums and products; multilinear expansion of det(XY) cancels repeated-column selections by pairing permutations differing by a transposition, and the remaining selections give det(X)det(Y). Cofactor expansion gives the adjugate identities, with off-diagonal entries vanishing by the same repeated-row or repeated-column cancellation. Pairwise cancellation is valid in every characteristic. The determinant of the empty matrix is 1.
4. Put d=det(c) and u=det(Q). Taking determinants in cQ=I gives du=1. Since H is commutative, also ud=1.
5. Form matrices X and Y over the commutative algebra H⊗H with entries X_ij=c_ij⊗1 and Y_ij=1⊗c_ij. Their product has entry Σ_l c_il⊗c_lj, so the comultiplication hypothesis says that the matrix obtained by applying Δ entrywise to c is XY. Since Δ and the two tensor inclusions are algebra homomorphisms, determinant multiplicativity and functoriality give Δ(d)=det(XY)=(d⊗1)(1⊗d)=d⊗d. Applying determinant functoriality to ε(c)=I similarly gives ε(d)=1.
6. Apply Δ to du=1. It follows that Δ(u) is an inverse of Δ(d)=d⊗d. The element u⊗u is also an inverse, because (d⊗d)(u⊗u)=du⊗du=1⊗1, and the reverse product is the same. Inverses are unique: if x and y are inverses of a, then x=x(ay)=(xa)y=y. Thus Δ(u)=u⊗u.
7. The adjugate identity and ud=1 show that c(u adj(c))=I. Since Qc=I, associativity gives Q=Q(c(u adj(c)))=(Qc)(u adj(c))=u adj(c). Taking entries proves S(c_ij)=u adj(c)_ij for every i,j.
8. Apply the antipode identity to Δ(d)=d⊗d, using ε(d)=1. This gives S(d)d=1. Since du=1, multiplication by u gives S(d)=u. Applying the algebra homomorphism S to du=1 now gives uS(u)=1. Multiplying by d and using du=1 gives S(u)=d.
9. The chosen u therefore satisfies du=1, Δ(u)=u⊗u, S(u)=d, and all the asserted entrywise antipode formulas. When n=0, d=u=1 and the entrywise statements are vacuous; the same determinant identities and Hopf unit identities cover this case.

## Key steps

1. Establish antipode multiplicativity by uniqueness of convolution inverses.
2. Apply the antipode identities entrywise to obtain Qc=I=cQ.
3. Set u=det(Q) and deduce det(c)u=1.
4. Factor the comultiplication matrix through the two tensor inclusions to prove Δ(det(c))=det(c)⊗det(c) and ε(det(c))=1.
5. Use uniqueness of inverses to prove Δ(u)=u⊗u.
6. Compare Q with u adj(c) using the adjugate identity.
7. Apply the antipode to the determinant identities to prove S(u)=det(c).

## Reference use

### local-project

Queries:
- `antipode.*(mul|one)|def antipode|antipodeAlgHom|exists.*(subcoalgebra|Subcoalgebra)|FiniteDimensional|finite.*[Cc]oalgebra`
- `FiniteDimensional|finiteDimensional|exists.*[Ss]ubcoalgebra|exists.*[Ss]ubcomodule|finite.*[Ss]ubcoalgebra`
- `theorem (det_mul|det_map|mul_adjugate|adjugate_mul)|def adjugate|theorem.*det.*one|map_det`
- `exists_extension|extend|exists.*basis|finite_basis|finBasis`
- `finiteType_adjoin|finiteType.*fg|fg.*finiteType|fg_adjoin|adjoin.*finite`
- `p05_fhe_(stable_subspace|coefficient_matrix|determinant_inverse)_a5b449214a`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p05_fhe_typecheck_a5b449214a.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean HeaderPolicyCheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/FiniteType.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge/HeaderPolicyCheck.lean`
- `/tmp/p05_fhe_typecheck_a5b449214a.lean`

The clean snapshots match project 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Coalgebra.Basic supplies finite tensor representations, coassociativity and counitality; the coalgebra-directory search found no finite-dimensional subcomodule existence theorem. Basis.VectorSpace supplies LinearMap.exists_extend. HopfAlgebra.Convolution already supplies antipodeAlgHom. The matrix files supply det_mul, RingHom.map_det, mul_adjugate and adjugate_mul; FiniteType supplies adjoin_of_finite. All three proposed types elaborated after import Submission under Lean 4.33.1. Kernel-checked diagnostic equalities confirmed ordinary multiplication for matrices constructed with Matrix.of. Audited infrastructure depends only on propext, Classical.choice and Quot.sound; all nine checked dependencies are clean and pinned. The existing private compiler copies were verified against policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: only listed lines 10–11 are omitted, original hash 2e81f3c63685285e1af52e3dee0c135a8a7c8e9f37be7ad076712f55790c632c reversibly yields build hash d10948155ea0e92408d3ce320bdd5db3b7f00b622f4c9de9c98f040a414fa2f6, and the rerun Lean probe confirmed every omitted target absent. The proposed names have no current DAG or searched library collisions. These are decomposition diagnostics, not comparator acceptance of theorem proofs.
