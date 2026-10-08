# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1`
- Child DAG node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.principal_cover_splitting-a1.clear_away_section-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put F=R^n. If 1=0 in R, every element x of every R-module satisfies x=1·x=0·x=0. Taking N=1 and the zero map t:M→F proves the conclusion. Hence assume R is nonzero. Let e_j be the standard basis of F and m_j=π(e_j). Surjectivity gives m=Σ_j x_j m_j whenever π(x)=m, so the m_j generate M. For each column index ℓ, write c_ℓ=Σ_j P_{jℓ}e_j. The kernel hypothesis gives π(c_ℓ)=0 and expresses every element of ker π as Σ_ℓ y_ℓ c_ℓ.
2. Put S=R[f⁻¹] and choose the assumed S-linear section σ:M_f→F_f. For every R-module X, its localization consists of fractions x/f^a. The fraction relation says x/f^a=y/f^b exactly when f^h(f^b x−f^a y)=0 for some h≥0. In particular x/1=0 exactly when some power of f annihilates x. No nonzero assumption on S is used.
3. For every j choose v'_j and a_j with σ(m_j/1)=v'_j/f^{a_j}. Let e be the maximum of these finitely many exponents, with maximum 0 for an empty family, and put v_j=f^{e−a_j}v'_j. The fraction relation gives σ(m_j/1)=v_j/f^e, hence v_j/1=f^e σ(m_j/1).
4. Set z_ℓ=Σ_j P_{jℓ}v_j. By the relation π(c_ℓ)=0 and S-linearity, z_ℓ/1=f^e σ((Σ_j P_{jℓ}m_j)/1)=0. For each ℓ select b_ℓ with f^{b_ℓ}z_ℓ=0, and let d be their maximum, taking 0 if p=0. Since f^d=f^{d−b_ℓ}f^{b_ℓ}, all f^d z_ℓ vanish. Define A:F→F by A(x)=Σ_j x_j(f^d v_j). This is R-linear and A(c_ℓ)=f^d z_ℓ=0. The column description of ker π therefore implies A vanishes on ker π.
5. For m∈M choose x with π(x)=m and define u(m)=A(x). If x' is another choice, x−x'∈ker π, so A(x)=A(x'). Thus u is well defined. Representatives x+x' and rx show additivity and scalar compatibility, respectively. Consequently u:M→F is R-linear and u(π(x))=A(x).
6. The induced S-linear map u_f satisfies u_f(m_j/1)=f^d v_j/1=f^{e+d}σ(m_j/1). These localized generators span M_f: if m=Σ_j x_jm_j, then m/f^a=Σ_j(x_j/f^a)(m_j/1). Thus u_f=f^{e+d}σ. Localization of linear maps sends x/f^a to its image divided by f^a and respects composition, subtraction and scalar multiplication. Therefore w=π∘u−f^{e+d}id_M localizes to zero, using π_f∘σ=id. In particular w(m_j)/1=0 for each j.
7. Choose c_j with f^{c_j}w(m_j)=0, and let c be their maximum, taking 0 if n=0. Then f^c w(m_j)=0 for all j, and R-linearity and generation by the m_j give f^c w=0 on M. Multiplying this equality by f yields f^{c+1}(π∘u)=f^{e+d+c+1}id_M. Set N=e+d+c+1 and t=f^{c+1}u. Then N>0 and π∘t=f^N id_M, which is exactly the required equality of R-linear maps. Empty generator or relation families were handled by the stated maximum convention, and S was allowed to be zero throughout.

## Key steps

1. Extract finite module generators and kernel generators from the presentation.
2. Use fraction representatives and the power-annihilation criterion for localization.
3. Choose a common denominator for the localized section on module generators.
4. Kill all relation errors by one power of f.
5. Descend the resulting linear map through π to obtain u:M→R^n.
6. Kill the remaining section error by one power using finite generation.
7. Rescale u once more to obtain π∘t=f^N id with N>0.

## Reference use

### local-project

Queries:
- `span_range_pow_eq_top|span_range_eq_top`
- `def map|map_mk|mk_eq_zero|mk_eq_mk|mk_surjective|exists.*eq|def lift|exists.*lift|eq_zero`
- `pcs_clear_away_section|pcs_patch_power_sections`
- `sed -n '1,210p' .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/LocalProperties/Projective.lean`
- `sed -n '259,340p' .humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Localization/Module.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean HeaderAbsence.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean CheckTypes.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/LocalizedModule/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Localization/Module.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Ideal/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/LocalProperties/Projective.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-principal-c-fd30309f6a/parent-child-handoff.json`
- `/tmp/p05-pcs-decomposition-at0a8zqn/latest-build/CheckTypes.lean`
- `/tmp/p05-pcs-decomposition-at0a8zqn/latest-CheckTypes.log`
- `/tmp/p05-pcs-decomposition-at0a8zqn/latest-HeaderAbsence.log`
- `/tmp/p05-pcs-decomposition-at0a8zqn/latest-interface-report.json`
- `/tmp/p05-pcs-decomposition-at0a8zqn/name-audit.json`
- `/tmp/p05-pcs-decomposition-at0a8zqn/pins.json`

The handoff identifies the supplied statement as the depth-3 principal_cover_splitting child of the frozen Hopf-kernel problem. The clean reference revisions are project 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine compiler dependencies also match clean pins. Relevant infrastructure includes LocalizedModule.mk_eq, induction_on, IsLocalizedModule.eq_zero_iff, the localization-linear map and its fraction formula, Ideal.span_range_pow_eq_top, and a maximal-localization splitting criterion. Both proposed literal types elaborate after import Submission; five anonymous checks verify matrix-vector multiplication, localization-ring linearity, the fraction formula, and scalar actions on linear maps. The six inspected library declarations have transitive axioms contained in propext, Classical.choice, and Quot.sound. Neither proposed name occurs in the ten DAG registries or imported environment. Final diagnostics bind to committed Submission snapshot ece863bfb9eb10d11de9b493e72d7f6223b12084. Disposable compiler copies omit exactly policy-listed lines 10–11 under policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96; Lean confirms all 13 targets absent. Exact omitted text and reversible hashes are recorded in latest-interface-report.json. These are interface checks, not proof acceptance; the configured comparator and independent review remain required.
