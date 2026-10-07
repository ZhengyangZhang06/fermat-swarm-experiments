# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.effective_domain-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put G=SL₂(ℤ). Finite index gives finitely many right cosets Δr. Choose exactly one representative of each and let R be their finite set. Define F=⋃_{r∈R}rF₀, where F₀=ModularGroup.fd. Write F₀°=ModularGroup.fdo.
2. The defining inequalities make F₀ closed relative to the upper half-plane. Every element of G acts by a homeomorphism, so each rF₀ is measurable and their finite union F is measurable. The set E=F₀\F₀° is contained in the two vertical lines x=±1/2 and the circle x²+y²=1. Each has planar measure zero: a line has zero area, and the vertical sections of the circle have at most two points, so Fubini gives zero area. The formula μ=dx dy/y² therefore gives μ(E)=0.
3. Möbius transformations preserve μ. Explicitly, for A=((a,b),(c,d)) with positive determinant, Im(Az)=det(A)Im(z)/|cz+d|² and its real Jacobian is det(A)²/|cz+d|⁴; these factors cancel in dx dy/y². This is also the invariant-measure instance in the pinned UpperHalfPlane/Measure.lean. Thus every translate aE is null. The group G is countable because its matrices have four integer entries, so N=⋃_{a∈G}aE is measurable, null, and G-invariant.
4. For any z, ModularGroup.exists_smul_mem_fd gives g∈G with gz∈F₀. Write g⁻¹=ηr with η∈Δ and r∈R. Then η⁻¹z=r(gz)∈F. Consequently there is γ∈Δ with γz∈F.
5. Fix z outside N and such a γ. Suppose δ∈Δ also has δz∈F. Choose r,s∈R and w,v∈F₀ with γz=rw and δz=sv. Since z is outside the G-invariant set N, neither w nor v belongs to E; in particular w∈F₀°. The matrix a=s⁻¹δγ⁻¹r satisfies aw=v∈F₀. By ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd, a=I or a=−I.
6. It follows that δγ⁻¹=sr⁻¹ or δγ⁻¹=−sr⁻¹. The left side belongs to Δ, and −I∈Δ, so sr⁻¹∈Δ in either case. Hence Δs=Δr. Uniqueness of the chosen coset representatives gives s=r, and then δγ⁻¹=I or −I. Thus δ=γ or δ=−γ.
7. Steps 4–6 establish the required representative property outside the null set N. Together with measurability from step 2, this proves the statement for the finite set R.

## Key steps

1. Choose finite representatives of the right cosets Δr.
2. Show the standard-domain boundary is hyperbolically null and its countable G-saturation remains null.
3. Use modular-domain covering to obtain a Δ-translate in the finite union.
4. Use interior uniqueness modulo ±I and uniqueness of coset representatives to prove the required almost-everywhere uniqueness.

## Reference use

### local-project

Queries:
- `rg --files .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb -g '*.lean' -g '*json' -g 'lean-toolchain' -g 'lakefile*'`
- `grep -R -n -E 'petersson|Petersson|InnerProductSpace.Core|IsFundamentalDomain' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `grep -R -n -E 'IsFundamentalDomain|integrable.*petersson|petersson.*integrable|heckeTLin.*[Ss]ymmet|[Ss]ymmet.*heckeTLin' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `grep -R -n -E 'f036cc6b1f_pc_effective_domain|f036cc6b1f_pc_integral_core|f036cc6b1f_pc_hecke_integral' .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes .humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json Submission.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `python3 /tmp/f036cc6b1f_petersson_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperator.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean`
- `/tmp/f036cc6b1f_petersson_contracts/CheckTypes.lean`
- `/tmp/f036cc6b1f_petersson_contracts/CheckTypes.log`
- `/tmp/f036cc6b1f_petersson_contracts/CheckInstances.log`
- `/tmp/f036cc6b1f_petersson_contracts/CheckCoreProjection.log`
- `/tmp/f036cc6b1f_petersson_contracts/CheckAxioms.log`
- `/tmp/f036cc6b1f_petersson_contracts/Submission.log`
- `/tmp/f036cc6b1f_petersson_contracts/ImportSubmissionCheck.log`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Installed mathlib matches that revision and has clean status; all compiled local dependency sources match the snapshot byte-for-byte. The attempted rg command failed because rg is unavailable, so searches used grep. No existing integrated fundamental-domain/Petersson-integrability/Hecke-symmetry result was found in the searched directories, and the proposed identifiers have no active-DAG collisions. The inspected sources supply modular-domain covering and interior uniqueness, cusp decay, Petersson covariance, hyperbolic measure invariance, the exact Hecke normalization, and Core fields. All three proposed types elaborate against Definitions.Def_ModularForm_HeckeOperatorForms with the project’s Lean options. Instance checks confirm UpperHalfPlane.instMeasureSpace, the SL action, the GL-invariant hyperbolic measure, and projection of the existential B in B.inner. Nine audited library declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. However, the required literal import Submission gate remains blocked: unchanged Submission.lean fails on the missing attribute targets FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions and FreyPackage.ModMCarrier.coe_rescaleLin_apply. No project source was modified; this is not comparator acceptance.
