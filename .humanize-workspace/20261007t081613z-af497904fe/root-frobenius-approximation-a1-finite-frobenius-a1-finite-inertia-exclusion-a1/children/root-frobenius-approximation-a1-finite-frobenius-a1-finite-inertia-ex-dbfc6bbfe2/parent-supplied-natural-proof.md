# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.integral_primitive-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E with the stated hypotheses. A finite ℚ-basis of E generates E as a field: the field containing the basis contains every rational linear combination of its elements. Every algebraic extension involved is separable. Indeed, an irreducible polynomial in characteristic zero has nonzero derivative of smaller degree, so it is relatively prime to its derivative.
2. We first show that two algebraic generators can be replaced by one. Let F = ℚ(a,b) ⊆ E and n = [F:ℚ]. There are exactly n rational embeddings F → Ω. To see this, extend embeddings along ℚ ⊆ ℚ(a) ⊆ ℚ(a,b). At each simple adjunction, an extension is determined by the image of the generator, which can be any root of the transported minimal polynomial. The quotient presentation by that minimal polynomial gives an embedding for each root. Separability gives exactly as many distinct choices as the degree, and multiplication of the two degrees gives n.
3. For two distinct such embeddings σ and τ, the equality σ(a+rb)=τ(a+rb), with r ∈ ℚ, has at most one solution if σ(b)≠τ(b). If σ(b)=τ(b), then σ(a)≠τ(a), since a and b generate F, so there is no solution. There are finitely many pairs of embeddings. Since ℚ is infinite, choose r outside all their exceptional values. Then c=a+rb has n distinct embedding images. All are roots of its rational minimal polynomial, so [ℚ(c):ℚ]≥n. The inclusion ℚ(c)⊆F gives the reverse inequality. The tower-degree formula therefore gives [F:ℚ(c)]=1, hence F=ℚ(c).
4. Repeatedly apply the preceding two-generator argument to a finite generating family for E. This produces θ ∈ E with ℚ(θ)=E. For the initial field ℚ one may take θ=0. Let p(X)=X^m+∑_{i<m} c_i X^i be the rational minimal polynomial of θ, where m≥1.
5. Choose a positive integer N divisible by the denominators of every c_i. Thus N c_i is an integer. For i<m, the coefficient N^(m−i)c_i is also an integer, because m−i≥1. Consequently g(X)=X^m+∑_{i<m} N^(m−i)c_i X^i belongs to ℤ[X] and is monic. With α=Nθ, direct substitution gives g(α)=N^m p(θ)=0. Thus α is integral over ℤ.
6. Since N is a nonzero rational number, α=Nθ lies in ℚ(θ), and θ=N⁻¹α lies in ℚ(α). Therefore ℚ(α)=ℚ(θ)=E. This α satisfies both required conclusions.

## Key steps

1. Obtain a finite generating family from a rational basis.
2. Count embeddings using separability and successive simple adjunctions.
3. Avoid finitely many rational parameters to replace two generators by one.
4. Inductively obtain a primitive element.
5. Clear denominators to make a nonzero integer multiple integral.
6. Use invertibility of the scaling rational number to preserve the generated field.

## Reference use

### local-project

Queries:
- `inertiaSubgroupIn|LiesOverPrime|primitive|discrim`
- `integral|nonunits|inertia|residue|decomposition`
- `theorem|lemma`
- `integral.*primitive|primitive.*integral`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/PrimitiveElement.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/tmp/p09-fie-decomposition-cq2vidxw/Interfaces.lean`
- `/tmp/p09-fie-decomposition-cq2vidxw/report.json`

The snapshot pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Field.exists_primitive_element supplies primitive generation; the scoped integral-primitive search found no match in PrimitiveElement.lean or NumberField/Basic.lean. minpoly.isIntegrallyClosed_eq_field_fractions' identifies the integral and rational minimal polynomials. MvPolynomial.esymmAlgHom_surjective supplies the integral symmetric-polynomial argument. ValuationSubring.coe_mem_nonunits_iff identifies ambient nonunits with the maximal ideal, while the project definition embeds the inertia kernel into rational automorphisms. Both proposed types elaborated after import Submission using Lean 4.33.1 and freshly compiled frozen Definitions. The inspected supporting declarations depend only on propext, Classical.choice and Quot.sound. The diagnostic records clean pinned dependencies, the matching header-policy digest, exact omitted lines, reversible original/build hashes, and successful absence checks for all eight targets. Original sources remained unchanged; these checks do not constitute proof acceptance.
