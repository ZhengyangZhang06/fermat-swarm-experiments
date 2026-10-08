# Parent-supplied natural-language proof

- Parent DAG node: `root.primitive_exists-a1.holomorphic_integral-a1`
- Child DAG node: `root.primitive_exists-a1.holomorphic_integral-a1.linepow_coefficient_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix n, z, and d. Write X=X₀ and Y=X₁. By definition, the underlying polynomial of linePow n z is (C(z)X+Y)^n. The binomial theorem in the commutative polynomial ring gives the finite expansion Σ_{r=0}^n C((binom(n,r):ℂ)z^r)X^rY^(n−r): indeed, (C(z)X)^r=C(z^r)X^r, and the natural binomial coefficient multiplies the scalar coefficient.
2. For 0≤r≤n define e_r=Finsupp.single 0 r+Finsupp.single 1 (n−r). Multiplication of monomials identifies the r-th summand of this expansion with monomial e_r ((binom(n,r):ℂ)z^r). Its coefficient at d is therefore (binom(n,r):ℂ)z^r if e_r=d and zero otherwise. Also e_r(0)=r and e_r(1)=n−r.
3. If d(0)+d(1)=n, let r=d(0). Then r≤n and n−r=d(1), so e_r=d by equality at the two elements of Fin 2. Any other equality e_s=d forces s=d(0) by evaluation at 0. Thus exactly one term contributes to the d coefficient of the expansion, giving (binom(n,d(0)):ℂ)z^(d(0)).
4. If d(0)+d(1)≠n, equality e_r=d would imply d(0)+d(1)=r+(n−r)=n for some r≤n, which is impossible. Every summand has zero coefficient at d, so the coefficient of the whole expansion is zero. These cases give the stated conditional formula. They also cover n=0, for which the binomial sum has only r=0.

## Key steps

1. Expand the underlying linePow polynomial by the binomial theorem.
2. Rewrite each summand as a monomial with exponent index e_r and scalar coefficient binom(n,r)z^r.
3. For degree-n indices, isolate the unique term r=d(0).
4. For all other indices, show every summand has zero coefficient.

## Reference use

### local-project

Queries:
- `def (BinaryForm|linePow|IsEichlerIntegral)|theorem.*(linePow|coeff)|IsHomogeneous`
- `coeff.*(add.*pow|X.*pow)|IsHomogeneous.coeff_eq_zero|isHomogeneous_monomial|coe_ofComplex|ofComplex_coe`
- `^((noncomputable )?(def|abbrev|theorem|lemma)) .*linePow.*coeff|^((noncomputable )?(def|abbrev|theorem|lemma)) .*coeff.*linePow`
- `p02_es_177ebb5a_hi_(prescribed_coefficients|linepow_coefficients)`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p02_177ebb5a_hi_decomposition_types.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_BinaryFormRep.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/project/Definitions/Def_HeckeEis_EichlerIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Algebra/MvPolynomial/Coeff.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/local-references/c882a7edc7dab33b/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p02/.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-scalar-primitive-a1/comparator-v2-integration-repair-1.log`
- `/tmp/p02_177ebb5a_hi_decomposition_types.lean`

The manifest pins project 1f74c284b125d4c45f527f2d621597fcf1e103a9 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. BinaryForm is the homogeneous submodule; linePow has underlying polynomial (C z * X 0 + X 1)^n; IsEichlerIntegral is exactly the coefficientwise derivative predicate. Homogeneous.lean supplies homogeneous monomials and finite sums. Coeff.lean supplies coeff_linearCombination_X_pow_of_fintype; no named specialized linePow coefficient theorem was found in the pinned project. Topology.lean supplies eventuallyEq_coe_comp_ofComplex. The inspected dependency files match the snapshot, and mathlib is clean at its pinned revision. Both proposed types elaborate after import Submission, with the final check exiting successfully. Audited library declarations use only propext, Classical.choice, and Quot.sound. Neither proposed name occurs in the inspected DAG. The inherited scalar-primitive node is marked proved and its recorded comparator reports acceptance with only those standard axioms.
