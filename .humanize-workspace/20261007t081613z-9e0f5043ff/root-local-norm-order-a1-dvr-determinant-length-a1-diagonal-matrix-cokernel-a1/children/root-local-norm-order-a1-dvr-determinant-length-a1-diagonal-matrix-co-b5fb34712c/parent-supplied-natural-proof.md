# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1.cokernel_invariant_under_units-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix R, m, D, P and Q with the stated hypotheses. Put V = R^(Fin m), A = P D Q, N = image(D), and N' = image(A). Matrix multiplication on column vectors defines R-linear maps because R is commutative.
2. Choose inverse matrices U and T for P and Q respectively. Thus UP = PU = 1 and TQ = QT = 1. Associativity of the matrix action shows that x ↦ Px and x ↦ Ux are mutually inverse linear maps on V; likewise x ↦ Qx and x ↦ Tx are mutually inverse.
3. Multiplication by P sends N into N'. Indeed, if n = Dy, then Pn = PDy = PDQ(Ty) = A(Ty), using QT = 1. Multiplication by U sends N' into N: if n' = Az, then Un' = UPDQz = D(Qz).
4. Define f : V/N → V/N' by f([x]) = [Px]. This is well-defined: if [x] = [y] modulo N, then x − y ∈ N, so P(x − y) ∈ N' by step 3, and therefore [Px] = [Py] modulo N'. The identities P(x + y) = Px + Py and P(rx) = r(Px) show that f preserves addition and scalar multiplication.
5. Define g : V/N' → V/N by g([x]) = [Ux]. The second containment in step 3 proves well-definedness by the same subtraction criterion. Linearity follows from U(x + y) = Ux + Uy and U(rx) = r(Ux).
6. For every x ∈ V, g(f([x])) = [UPx] = [x] and f(g([x])) = [PUx] = [x]. Every quotient element has a representative, so these identities hold on both entire quotients. Thus f and g are mutually inverse R-linear maps, providing the required linear equivalence and hence its Nonempty witness. All arguments remain valid when m = 0.

## Key steps

1. Choose two-sided matrix inverses for P and Q.
2. Show P sends image(D) into image(P D Q), using the inverse of Q.
3. Show the inverse of P sends image(P D Q) into image(D).
4. Descend P and its inverse to well-defined linear maps between the quotients.
5. Check the descended maps are mutually inverse on quotient representatives.

## Reference use

### local-project

Queries:
- `rg -n --glob '*.lean' 'cokernel.*(isUnit|IsUnit|diagonal)|[Dd]iagonal.*[Cc]okernel|[Cc]okernel.*[Dd]iagonal|range_mulVecLin.*pi|mulVecLin.*quot' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f`
- `rg -n 'quotientEquiv|quotEquivOfEq|mapQ' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`
- `rg -n 'span_singleton|mk_surjective|eq_zero_iff_mem' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Quotient/Defs.lean .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Span.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Quotient/Pi.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/LinearAlgebra/Isomorphisms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Span.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Ideal/Quotient/Defs.lean`

No exact matrix-cokernel theorem matched the targeted search. Relevant infrastructure includes Matrix.mulVecLin_mul, Matrix.toLinearEquiv', Submodule.Quotient.equiv, Submodule.quotientPi, LinearMap.quotKerEquivOfSurjective, and principal-ideal membership and quotient-surjectivity lemmas. Inspected sources match installed mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all installed dependencies matched their pins and had clean tracked files. Transitive axiom checks of these library declarations reported only propext, Classical.choice, and Quot.sound. Both proposed types elaborated with Lean 4.33.1 through the existing import-only Submission interface; matrix instances synthesized as Matrix.semiring.toMonoid and Matrix.instMulOfFintypeOfAddCommMonoid. The full frozen Submission has pre-existing unknown attribute targets, so this interface check is not full-contract or comparator acceptance.
