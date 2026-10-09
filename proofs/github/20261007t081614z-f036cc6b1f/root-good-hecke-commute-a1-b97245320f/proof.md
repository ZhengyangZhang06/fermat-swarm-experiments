# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.good_hecke_commute-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix M ≠ 0 and primes p,r not dividing M, with arbitrary witnesses of these conditions. Write V = S₂(Γ₀(M)) and T_s = CuspForm.heckeTLin 2 hs hsM for a good prime s. The translation matrix ((1,1),(0,1)) belongs to Γ₀(M), so every f ∈ V is 1-periodic. Infinity is a cusp, as this translation is a nontrivial parabolic fixing it. Thus f is holomorphic and tends to zero at infinity, in particular is bounded there. The same holds for every T_s f because the exact operator is bundled as a cusp form.
2. Periodicity lets f descend under q = exp(2πiz) to a well-defined holomorphic function F on the punctured unit disk. Local logarithms establish holomorphy, and boundedness at infinity removes the singularity at zero. Taylor expansion yields f(z) = Σₙ≥0 aₙ(f)exp(2πinz), absolutely convergent for every z in the upper half-plane. Uniqueness of Taylor coefficients gives uniqueness of these coefficients; equality of all coefficients implies equality of the functions. These facts are precisely the relevant results of the pinned QExpansion.lean, including UpperHalfPlane.hasSum_qExpansion and UpperHalfPlane.qExpansion_coeff_unique.
3. For a prime s, positivity gives s ≠ 0. The definitions in Def_ModularForm_HeckeOperator.lean give the weight-two slash contributions s⁻¹f((z+j)/s) and s f(sz). The coercion theorem CuspForm.coe_heckeTLin_apply in Def_ModularForm_HeckeOperatorForms.lean therefore gives the exact pointwise identity T_s f(z) = s⁻¹Σ_{0≤j<s} f((z+j)/s) + s f(sz). In particular, no independent normalization has been introduced.
4. Substitute the absolutely convergent expansion from step 2 into this identity. In the finite translation sum the term with index m is multiplied by s⁻¹Σ_{0≤j<s} exp(2πimj/s). If s divides m, this multiplier is one. Otherwise q = exp(2πim/s) satisfies q^s = 1 and q ≠ 1; the identity (1−q)Σ_{j=0}^{s−1}q^j = 1−q^s forces the sum to be zero. Thus only m = sn survives, contributing a_{sn}(f) at index n. The term s f(sz) contributes s a_{n/s}(f) when s divides n and zero otherwise. Finite summation and absolute convergence justify the rearrangement. Uniqueness from step 2 proves, for every n ≥ 0, aₙ(T_s f) = a_{sn}(f) + s a_{n/s}(f) if s divides n, and aₙ(T_s f) = a_{sn}(f) otherwise.
5. If p = r, the two endomorphisms are equal: the underlying formula depends only on that prime and f, and proof witnesses are irrelevant. Their composites therefore agree. Suppose henceforth that p ≠ r. Distinct primes are coprime. In particular r divides pn exactly when r divides n, and p divides rn exactly when p divides n. If p divides n, then r divides n/p exactly when pr divides n; the analogous assertion holds with p and r interchanged. Whenever p divides n, r(n/p) = (rn)/p; whenever r divides n, p(n/r) = (pn)/r. Successive divisions under pr divisibility both equal n/(pr). These are integer identities obtained by writing n as the corresponding multiple.
6. Apply the coefficient formula twice to T_p(T_r f). The result at index n is a_{prn}(f), plus r a_{pn/r}(f) when r divides n, plus p a_{rn/p}(f) when p divides n, plus pr a_{n/(pr)}(f) when pr divides n. The divisibility and quotient identities in step 5 give exactly these conditions and indices. Applying the formula twice to T_r(T_p f) produces the same four terms, with their order interchanged. These computations also apply at n = 0, since every positive integer divides zero and the quotients are zero. Thus every coefficient of the two composites agrees.
7. Step 2 implies equality of their underlying functions for every f ∈ V. Extensionality of bundled cusp forms gives T_p(T_r f) = T_r(T_p f), and extensionality of linear maps gives T_p.comp T_r = T_r.comp T_p. All arguments used the exact bundled operators and arbitrary witnesses, so this is the stated theorem.

## Key steps

1. Obtain unique absolutely convergent period-one expansions for cusp forms and their Hecke images.
2. Use the frozen slash normalization to identify the exact pointwise Hecke formula.
3. Evaluate the finite roots-of-unity sum to derive the coefficient formula.
4. Handle equal primes by proof irrelevance and distinct primes by coprimality.
5. Show the two composites have identical four-term coefficient expressions.
6. Apply Fourier uniqueness and bundled extensionality to obtain equality of linear-map compositions.

## Reference use

### local-project

Queries:
- `rg -n 'heckeTLin|InnerProductSpace.Core|iSup_iInf_eq_top_of_commute|sturm_bound_levelOne_nat' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb`
- `grep -RnE 'finiteDimensional|FiniteDimensional|InnerProductSpace.Core|heckeTLin.*commut|heckeTLin.*[Ss]ymmet'`
- `grep -nE 'Gamma0|FiniteIndex|Normal'`
- `grep -nE 'iSup_iInf_eq_top_of_commute|sturm_bound_levelOne_nat|hasSum_qExpansion|qExpansion_coeff_unique|instFiniteIndexGamma0|petersson_slash|structure InnerProductSpace.Core|eq_one_or_neg_one_of_mem_fdo_mem_fd'`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `#print axioms CuspForm.heckeTLin`
- `#print axioms ModularForm.heckeT_apply`
- `#print axioms CongruenceSubgroup.instFiniteIndexGamma0`
- `#print axioms UpperHalfPlane.hasSum_qExpansion`
- `#print axioms LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`
- `#print axioms ModularForm.sturm_bound_levelOne_nat`
- `#print axioms UpperHalfPlane.petersson_slash`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperator.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean`
- `/tmp/fermat_p01_decomposition_a90tkggj/CheckDependencyTypes.lean`
- `/tmp/fermat_p01_decomposition_a90tkggj/CheckDependencyTypes.log`
- `/tmp/fermat_p01_decomposition_a90tkggj/CheckLibrary.log`
- `/tmp/fermat_p01_decomposition_a90tkggj/Submission.log`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The installed mathlib has that revision and clean status; the compiled project dependency sources match the snapshot byte-for-byte. ripgrep is unavailable, so the attempted rg search was followed by grep and Python file inspection. The sources establish the exact Hecke normalization, finite index, Fourier expansion and uniqueness, level-one Sturm bound, Petersson covariance, invariant measure, InnerProductSpace.Core, and the arbitrary-family simultaneous-eigenspace theorem. No suitable Gamma0 finite-dimensionality or bundled Hecke symmetry/commutation theorem was found in the searched Definitions and mathlib modular-form directories. All seven audited declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. The three proposed types elaborate against the unchanged contract imports; an anonymous rfl check confirms that the inner-product instance induced from B has inner product B.inner. However, literal import Submission validation is blocked: unchanged Submission.lean fails at its attribute commands with unknown constants FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions and FreyPackage.ModMCarrier.coe_rescaleLin_apply. No project source was changed.
