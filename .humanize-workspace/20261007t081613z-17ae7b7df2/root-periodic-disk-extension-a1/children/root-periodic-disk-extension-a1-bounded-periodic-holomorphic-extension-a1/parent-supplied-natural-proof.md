# Parent-supplied natural-language proof

- Parent DAG node: `root.periodic_disk_extension-a1`
- Child DAG node: `root.periodic_disk_extension-a1.bounded_periodic_holomorphic_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix w,g and the stated hypotheses. Write D={q:‖q‖<1}, D*=D\{0}, and Q(z)=exp(2πiz/w). The exponential norm identity gives ‖Q(z)‖=exp(−2π Im z/w), and Q(z)≠0. Thus Q maps H into D*. Conversely, if q∈D*, choose L=Complex.log q. The identity Complex.exp_log gives exp L=q. Set z=wL/(2πi). Then Q(z)=q and Im z=−w log‖q‖/(2π)>0. More generally every preimage of q has this height, by taking the real logarithm of the norm identity.
2. If z,z'∈H and Q(z)=Q(z'), Complex.exp_eq_exp_iff_exists_int gives z=z'+nw for some integer n. Real translation preserves imaginary parts. The given periodicity therefore implies g(z+nw)=g(z) for n≥0 by induction. Applying periodicity at z−w gives g(z−w)=g(z), and induction gives the same invariance for negative integers. Hence g is constant on each fiber of Q in H. Define F(q) on D* to be g(z) for any such preimage, and define F arbitrarily, say as zero, elsewhere. This is well-defined and F(Q(z))=g(z) on H.
3. We establish a holomorphic local logarithm without assuming that the principal logarithm is holomorphic across its branch cut. On |u|<1 put S(u)=∑_{n≥1}(−1)^{n+1}uⁿ/n. On every closed disk |u|≤s<1, the series and its formal derivative series converge uniformly, with bounds sⁿ and sⁿ⁻¹. The derivative series sums to 1/(1+u). Apply the fundamental theorem of calculus to polynomial partial sums along segments and pass to the uniform limits. This gives S(v)−S(u)=(v−u)∫₀¹1/(1+u+t(v−u))dt. Dividing by v−u and letting v tend to u proves S'(u)=1/(1+u). The integrands are continuous on compact intervals, so the integrals exist; the applicable pinned result is intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le in Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1140.
4. Fix q₀∈D* and choose L₀ with exp L₀=q₀. For |q−q₀|<|q₀| set L(q)=L₀+S((q−q₀)/q₀). Step 3 gives L'(q)=1/q. The function exp(L(q))/q therefore has derivative zero on this disk, which excludes zero. Along every segment from q₀ its derivative is zero, so the fundamental theorem gives a constant value, namely exp L₀/q₀=1. Consequently exp L(q)=q. Restrict to a smaller disk also contained in D. Then z(q)=wL(q)/(2πi) is holomorphic and takes values in H by the height formula. Fiber independence gives F(q)=g(z(q)) there. Thus F is holomorphic throughout D*.
5. Choose C,Y from boundedness and let H₀=max(1,Y+1), M=max(C,0), and r=exp(−2πH₀/w). Then 0<r<1. For 0<‖q‖<r, every preimage in step 1 has height greater than H₀ and hence greater than Y. Thus ‖F(q)‖≤C≤M on this punctured disk.
6. Define B(q)=q²F(q) for q≠0 and B(0)=0. It is holomorphic on D*. Near zero the bounds ‖B(q)‖≤M‖q‖² and ‖B(q)/q‖≤M‖q‖ imply continuity at zero and complex differentiability there with derivative zero. Hence B is holomorphic on all of D, with B(0)=B'(0)=0.
7. By DifferentiableOn.analyticAt in Mathlib/Analysis/Complex/CauchyIntegral.lean:625, B has a convergent Taylor expansion B(q)=∑_{n≥0}bₙqⁿ on some disk of radius R>0. Choose 0<t<R. Convergence at the positive real point t gives a constant K with |bₙ|tⁿ≤K for every n. On every radius-s disk with s<t, these estimates bound the derivative series by a summable geometric series times n. The uniform-limit argument of step 3 therefore justifies differentiation and gives b₀=B(0)=0 and b₁=B'(0)=0. Define C₀(q)=∑_{n≥0}bₙ₊₂qⁿ for |q|<t. On |q|≤s<t its terms are bounded by Kt⁻²(s/t)ⁿ and its derivative terms by Kt⁻³n(s/t)ⁿ⁻¹. Both bounds are summable, so C₀ is holomorphic. Multiplying the series by q² gives q²C₀(q)=B(q), and hence C₀(q)=F(q) for 0<|q|<t.
8. Set A(0)=C₀(0), set A(q)=F(q) on D*, and set A(q)=0 outside D. Near zero A agrees with C₀; at every other point of D it locally agrees with F. Therefore A is holomorphic on D. For z∈H, Q(z)∈D*, so A(Q(z))=F(Q(z))=g(z), proving the required conclusion.

## Key steps

1. Establish the exponential coordinate's image, surjectivity, and preimage-height formula.
2. Use integer-shift invariance to descend g to the punctured disk.
3. Construct local logarithms by a uniformly differentiable power series and prove holomorphy of the descent.
4. Transfer the high-half-plane bound to a punctured neighborhood of zero.
5. Multiply by q², prove differentiability at zero, and remove the first two zero Taylor coefficients.
6. Patch the Taylor quotient with the punctured-disk function to obtain A and its factorization.

## Reference use

### local-project

Queries:
- `qParam|cuspFunction|analyticOrderAt|periodic_disk_extension|pde_holomorphic_extension|pde_finite_order|pde_decay_zero`
- `removable|differentiableOn|bounded|exists|limUnder`
- `analyticOrderAt_eq_top|eqOn_zero|eqOn_of_preconnected|exists_eventuallyEq_pow|analyticAt`
- `exp_log|exp_eq_exp_iff_exists_int`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_GenusNumerics.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/project/Definitions/Def_ModularCurve_X0.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/Periodic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/RemovableSingularity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/Analytic/Order.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p10/.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/local-references/a3694b60efa3c29f/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`

The snapshot records project a97febc53b1c4d489edc54ca44132af7a21279b3 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Periodic.lean supplies the q-parameter norm, inverse, and descent API; its global-periodicity hypotheses must not be confused with the parent's periodicity restricted to the upper half-plane. RemovableSingularity.lean provides bounded removable singularities. CauchyIntegral.lean:625 supplies holomorphic-to-analytic conversion; IsolatedZeros.lean:185 supplies local factorization; Order.lean:86,101 identifies the two orders. Log.lean:41,171 supplies exponential surjectivity onto nonzero complex numbers and its integer-period fibers. FundThmCalculus.lean:1140 supports the segment argument. The search found no matching analytic-extension or analytic-order lemma in Def_ModularCurve_GenusNumerics.lean. Inspected mathematical sources match the installed pinned sources; all nine dependencies were clean and matched their pins. The checked library declarations depend only on propext, Classical.choice, and Quot.sound.
