# Parent-supplied natural-language proof

- Parent DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1`
- Child DAG node: `root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1.diagonal_cokernel_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix R, m and d. Write V = R^(Fin m), I_i = Ideal.span({d(i)}), W = ∏_i R/I_i, and N = image(diagonal(d)). Multiplication by diagonal(d) sends z ∈ V to the vector whose i-th coordinate is d(i)z(i).
2. Define C : V → W by C(y)(i) = [y(i)] modulo I_i. Each coordinate quotient map preserves addition and scalar multiplication, so C is R-linear.
3. If y ∈ N, choose z with y = diagonal(d)z. Then y(i) = d(i)z(i) belongs to I_i for every i. Hence every coordinate of C(y) is zero, proving N ⊆ ker(C).
4. Conversely, if C(y) = 0, then y(i) ∈ I_i for every i. The principal ideal I_i consists exactly of the multiples of d(i): these multiples form an ideal containing d(i), and every ideal containing d(i) contains all its multiples. Consequently, choose z(i) with y(i) = d(i)z(i) for each i, using commutativity if the multiple is initially written in the opposite order. Assemble these witnesses into z ∈ V. The coordinate formula in step 1 gives y = diagonal(d)z, so y ∈ N. Therefore ker(C) = N.
5. The map C is surjective. Given w ∈ W, choose a representative y(i) ∈ R for each quotient class w(i), and assemble them into y ∈ V. Then C(y) = w by equality of all coordinates.
6. Define the induced map C̄ : V/N → W by C̄([y]) = C(y). If two representatives differ by an element of N, their C-images differ by zero by step 3; thus C̄ is well-defined. The addition and scalar identities for C descend to C̄, so C̄ is linear.
7. If C̄([y]) = C̄([z]), linearity gives C(y − z) = 0. Step 4 yields y − z ∈ N, hence [y] = [z]. Thus C̄ is injective. Step 5 gives surjectivity by taking the class of a representative preimage.
8. Let G assign to each element of W its unique preimage under C̄. For w and w' in W, linearity gives C̄(G(w) + G(w')) = w + w', so uniqueness implies G(w + w') = G(w) + G(w'). Similarly C̄(rG(w)) = rw implies G(rw) = rG(w). Thus G is linear and is inverse to C̄, providing the required linear equivalence and Nonempty witness. When m = 0, all coordinate choices and coordinate equalities are empty and the same construction applies.

## Key steps

1. Construct the coordinatewise quotient linear map.
2. Show the diagonal image lies in its kernel.
3. Use principal-ideal membership witnesses to prove the reverse kernel inclusion.
4. Choose coordinate representatives to prove surjectivity.
5. Descend to the quotient by the diagonal image.
6. Prove the induced map is bijective and its inverse is linear.

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
