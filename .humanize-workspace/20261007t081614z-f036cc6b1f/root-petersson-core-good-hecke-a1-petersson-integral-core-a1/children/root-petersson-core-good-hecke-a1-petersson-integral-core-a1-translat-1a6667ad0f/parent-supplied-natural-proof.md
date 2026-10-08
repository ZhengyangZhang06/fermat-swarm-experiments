# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Δ,r,f,g as stated, and put H=r⁻¹Δr. Conjugation preserves finite index. Let T be the integral determinant-one translation matrix acting by z↦z+1. Since H has finitely many cosets, two distinct nonnegative powers T^i,T^j, with i<j, represent the same coset. Their quotient is T^h∈H for h=j−i>0. This nontrivial parabolic fixes infinity, so infinity is a cusp of H and r∞ is a cusp of Δ.
2. Set u=f|₂r and v=g|₂r. The slash formula and holomorphy of f,g show that u,v are holomorphic on ℍ. Since rT^hr⁻¹∈Δ, slash invariance and the slash composition law give u(z+h)=u(z) and v(z+h)=v(z). Vanishing of f,g at the cusp r∞ gives u(z),v(z)→0 as Im z→∞, uniformly in Re z. These are the translated cusp conditions, also expressed by CuspForm.translate and CuspFormClass.zero_at_infty_slash in the pinned Basic.lean.
3. For q=exp(2πiz/h), equality of q-values is equivalent to the two arguments differing by an integral multiple of h. Hence periodicity makes u descend to a well-defined holomorphic function u₀ on 0<|q|<1; local logarithms show holomorphy. Since |q|=exp(−2π Im z/h), the uniform zero limit of u makes u₀ tend to zero at q=0. The removable-singularity theorem extends u₀ holomorphically across zero, with u₀(0)=0. The quotient U(q)=u₀(q)/q extends holomorphically at zero with value u₀′(0). The identical argument gives v₀(q)=qV(q) with V holomorphic on the unit disk. This is the argument behind UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty in the pinned QExpansion.lean.
4. Continuity on the compact disk |q|≤1/2 supplies nonnegative constants Cᵤ,Cᵥ bounding |U| and |V| there. Choose Y≥1 such that exp(−2πY/h)≤1/2. For every z=x+iy with y≥Y, we have |u(z)v(z)|≤CᵤCᵥ exp(−ay), where a=4π/h>0. Thus the planar integral of |uv| over F₀∩{y≥Y} is at most CᵤCᵥ times the integral of exp(−ay) over [−1/2,1/2]×[Y,∞), which equals CᵤCᵥ exp(−aY)/a and is finite.
5. If z=x+iy belongs to F₀, then x²+y²≥1 and x²≤1/4, so y≥√3/2. Therefore F₀∩{y≤Y} lies in the compact rectangle [−1/2,1/2]×[√3/2,Y], entirely inside ℍ. Continuity of u,v bounds |uv| on this rectangle. Its planar area is finite, so the planar integral of |uv| on the lower part is finite. Together with step 4 this proves that the planar integral of |uv| over F₀ is finite. All these sets are measurable, since the defining coordinate inequalities are closed or open inequalities of continuous functions.
6. For r with lower row (c,d), the determinant-one slash formula gives u(z)=(cz+d)⁻²f(rz), and similarly for v, while Im(rz)=Im(z)/|cz+d|². Direct substitution gives P(u,v)(z)=P(f,g)(rz), the identity UpperHalfPlane.petersson_slash_SL. The Möbius map z↦rz is a measure-preserving homeomorphism for μ by the pinned UpperHalfPlane/Measure.lean. Changing variables therefore gives ∫⁺_{rF₀}|P(f,g)|dμ=∫⁺_{F₀}|u(z)v(z)|(Im z)²dμ. In μ=dx dy/y², the positive factor y² cancels the density, so the last integral is exactly the finite planar integral obtained in step 5.
7. The function P(f,g) is continuous, hence strongly measurable as a complex-valued function. The image rF₀ is measurable because the action is a homeomorphism. The finite integral of its norm established in step 6 proves the asserted complex Bochner integrability on rF₀.

## Key steps

1. Obtain a positive translation period in r⁻¹Δr from finite index.
2. Translate the cusp forms and deduce holomorphy, periodicity, and uniform vanishing at infinity.
3. Descend through q=exp(2πiz/h), remove the singularity at zero, and factor out q.
4. Bound the high-domain planar integral by an integrable exponential.
5. Bound the remaining part using its containment in a compact rectangle.
6. Use Petersson covariance and hyperbolic-measure invariance to transfer the finite norm integral to rF₀.
7. Combine continuity with finite norm integral to conclude integrability.

## Reference use

### local-project

Queries:
- `rg -n 'integrable.*petersson|petersson.*integrable|integral.*petersson|petersson.*integral|IsOpenPosMeasure' project/Definitions mathlib/Mathlib/NumberTheory/ModularForms mathlib/Mathlib/Analysis/Complex/UpperHalfPlane`
- `exp_decay|cuspFunction|hasSum|zero_at|IsCusp|FiniteIndex|translate`
- `def fd|def fdo|isClosed_fd|sqrt|im.*fd|mem_fd`
- `SL_neg_smul|coeSubgroup|coe.*Subgroup|instCoe`
- `f036cc6b1f_pic_translated_integrable|f036cc6b1f_pic_domain_transfer|f036cc6b1f_pic_diagonal_definite`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `python3 /tmp/f036cc6b1f_integral_core_split/verify.py`
- `tail -8 /tmp/f036cc6b1f_integral_core_split/CheckInfrastructure.log`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean`
- `/tmp/f036cc6b1f_integral_core_split/verify.py`
- `/tmp/f036cc6b1f_integral_core_split/CheckTypes.lean`
- `/tmp/f036cc6b1f_integral_core_split/CheckTypes.log`
- `/tmp/f036cc6b1f_integral_core_split/CheckInfrastructure.lean`
- `/tmp/f036cc6b1f_integral_core_split/CheckInfrastructure.log`

The snapshot pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. All nine installed package revisions match their pins and have clean working trees. The inspected mathlib sources and all twenty local dependency modules rebuilt for this check match the snapshot. QExpansion.lean supplies the removable-singularity and exponential-decay arguments; Petersson.lean supplies continuity and covariance; Measure.lean defines the unnormalized hyperbolic measure and proves GL₂(ℝ)-invariance; Modular.lean supplies the domain geometry. The targeted search found no matching Petersson-integrability/integral or IsOpenPosMeasure declarations in the searched directories. All three proposed types elaborate after literal import Submission. Instance inspection confirms UpperHalfPlane.instMeasureSpace, UpperHalfPlane.SLAction.toSMul, matrix multiplication in GL₂(ℝ), and the subgroup embedding Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ). Twelve audited infrastructure declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. The proposed names have no active-DAG collisions. These checks establish interface compatibility, not comparator acceptance of the proposed child proofs.
