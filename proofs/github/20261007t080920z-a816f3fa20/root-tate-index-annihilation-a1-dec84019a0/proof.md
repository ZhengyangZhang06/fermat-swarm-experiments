# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.tate_index_annihilation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, G, A, H, q and the stated zero-object hypothesis. Put d = [G:H]. If a module is a zero object, its identity and zero endomorphisms agree; evaluating this equality shows that every element is zero. Thus the hypothesis makes the restricted degree-q Tate module zero elementwise. We will construct, in each degree, linear maps from the ambient Tate module to the restricted Tate module and back whose composite is d times the identity.

2. For L equal to G or H, with the corresponding action on A, let A^L be the invariant submodule. Let I_L be the k-submodule spanned by all la − a, and set A_L = A/I_L. Write [a]_L for the class of a. Define N_L(a) = ∑_{l∈L} la. Left multiplication permutes L, so N_L(a) is invariant. Right multiplication permutes L, so N_L(la − a) = 0. Therefore N_L induces ν_L : A_L → A^L. Since every coinvariant class has a representative, the image of ν_L is exactly the image of N_L viewed inside A^L. These are the coinvariants and normBar appearing in the frozen definition. That definition identifies Tate degree j with H^j(L,A) for j ≥ 1, with A^L/im(ν_L) for j = 0, with ker(ν_L) for j = −1, and with H_{−j−1}(L,A) for j ≤ −2.

3. Choose a set T containing one representative of each left coset tH and a set S containing one representative of each right coset Hs. Cosets partition the finite group, so multiplication gives bijections T × H → G and H × S → G. Indeed every element has the required expression, and equality of two expressions first forces equality of the represented cosets, then equality of the representatives and of the remaining H factors. Inversion bijects left and right cosets. Consequently both T and S have d elements. In choosing S, take 1 as the representative of H.

4. For a group L, define B(L)_n to be the free k-module on tuples (g₀,…,g_n) of elements of L, with diagonal left action. Its differential for n ≥ 1 is ∂(g₀,…,g_n) = ∑_{i=0}^n (−1)^i(g₀,…,ĝ_i,…,g_n), and its degree-zero differential is zero. These maps are equivariant. The composite differential is zero: for i < j, deleting the original positions i and j in the two possible orders produces the same tuple with signs (−1)^{i+j−1} and (−1)^{i+j}. All terms cancel in pairs.

5. The cochain complex Hom_L(B(L),A) identifies with the defining inhomogeneous cochain complex. Explicitly, an equivariant cochain F corresponds to f(x₁,…,x_n) = F(1,x₁,x₁x₂,…,x₁⋯x_n). Conversely set F(g₀,…,g_n) = g₀ f(g₀⁻¹g₁,g₁⁻¹g₂,…,g_{n−1}⁻¹g_n). Adjacent ratios are unchanged by simultaneous left translation, proving equivariance of the inverse formula. The formulas are inverse by substitution and extend uniquely to linear maps on the free modules. Deleting the first vertex gives x₁f(x₂,…,x_{n+1}); deleting an interior vertex multiplies the two adjacent ratios; deleting the last vertex drops the last ratio. Thus the coboundary is x₁f(x₂,…,x_{n+1}) + ∑_{i=1}^n (−1)^i f(x₁,…,x_ix_{i+1},…,x_{n+1}) + (−1)^{n+1}f(x₁,…,x_n). This is the differential defining groupCohomology in the pinned GroupCohomology/Basic.lean. The formulas also cover n = 0 using empty tuples.

6. The complex (A ⊗_k B(L))_L, with diagonal action before taking coinvariants, identifies with the defining inhomogeneous chain complex. Send [a ⊗ (g₀,…,g_n)]_L to the chain with coefficient g₀⁻¹a at the tuple (g₀⁻¹g₁,…,g_{n−1}⁻¹g_n). Simultaneous translation of a and all g_i by l leaves both this coefficient and these ratios unchanged, so the map respects coinvariants. It extends linearly and respects tensor relations because the action is k-linear. Its inverse sends the chain with coefficient a at (x₁,…,x_n) to [a ⊗ (1,x₁,x₁x₂,…,x₁⋯x_n)]_L. One composite is immediately the identity; for the other, translating by g₀⁻¹ normalizes the first vertex to 1 and proves equality of the coinvariant classes. The induced boundary on a[x₁,…,x_n] is (x₁⁻¹a)[x₂,…,x_n] + ∑_{i=1}^{n−1}(−1)^i a[x₁,…,x_ix_{i+1},…,x_n] + (−1)^n a[x₁,…,x_{n−1}]. This is the defining differential in the pinned GroupHomology/Basic.lean, including the inverse action in its first term. The degree-zero differential is zero in both complexes.

7. We next justify computing the H groups using B(G). The unique expression g = hs with h ∈ H and s ∈ S defines r(g) = h. Uniqueness shows r(hg) = h r(g), and the choice of representative 1 for H shows r(h) = h. Let i : H → G be inclusion. Coordinatewise application defines H-equivariant chain maps r_* : B(G) → B(H) and i_* : B(H) → B(G), because coordinatewise maps commute with deleting vertices. Their composite r_*i_* is the identity.

8. Set u = id_G and v = i ∘ r. Define D_n(g₀,…,g_n) = ∑_{j=0}^n (−1)^j(ug₀,…,ug_j,vg_j,…,vg_n), extending k-linearly. Both u and v are H-equivariant, hence D_n is H-equivariant. We verify ∂D_n + D_{n−1}∂ = v_* − u_*, where D_{−1} = 0. In the jth summand, deleting position k < j cancels the term obtained by first deleting g_k and then taking the (j−1)st prism summand: their signs are (−1)^{j+k} and (−1)^{j+k−1}. Deleting position k > j+1 cancels the term obtained by first deleting g_{k−1} and then taking the jth prism summand; those signs are (−1)^{j+k} and (−1)^{j+k−1}. Every term of D_{n−1}∂ occurs in one of these pairings. The two remaining deletions in the jth summand give +(ug₀,…,ug_{j−1},vg_j,…,vg_n) and −(ug₀,…,ug_j,vg_{j+1},…,vg_n). Summing over j telescopes to the all-v tuple minus the all-u tuple. This calculation also applies for n = 0.

9. Applying Hom_H(−,A) to these maps produces inverse maps on cohomology. In fact, for a cocycle f, precomposition with v_* − u_* gives f(∂D + D∂) = (fD)∂, which is a coboundary; in degree zero the absent negative-degree term is zero. Likewise, tensor the chain maps and D with A and pass to H-coinvariants. This is permitted by H-equivariance. For a cycle z the difference between the two induced endomorphisms is ∂Dz, a boundary. Thus the resulting maps induce inverse homology maps. Together with steps 5 and 6, this proves that Hom_H(B(G),A) computes H^n(H,A), and (A ⊗_k B(G))_H computes H_n(H,A), for every n ≥ 0. The same statements for G follow directly from steps 5 and 6. All identifications are k-linear.

10. On the common cochain complex B(G), let R send a G-equivariant cochain to the same cochain regarded as H-equivariant. For an H-equivariant cochain f, define (Cf)(b) = ∑_{t∈T} t f(t⁻¹b). The summand depends only on tH: replacing t by th gives th f(h⁻¹t⁻¹b) = t f(t⁻¹b). For g ∈ G, the representatives gt form another left transversal. Using these to evaluate Cf(gb) gives ∑_t gt f(t⁻¹b) = g Cf(b). Hence Cf is G-equivariant. Both R and C are k-linear.

11. Since ∂ commutes with the G-action, C(f ∘ ∂) = (Cf) ∘ ∂; R also commutes with the coboundary. Thus both maps send cocycles to cocycles and coboundaries to coboundaries and induce maps on cohomology. If f is G-equivariant, every summand t f(t⁻¹b) equals f(b), so CRf = d f. Consequently, after the identifications in step 9, the induced maps H^n(G,A) → H^n(H,A) → H^n(G,A) have composite d times the identity in every degree n ≥ 0.

12. For any k-linear G-representation W, define π : W_H → W_G by π([w]_H) = [w]_G. It is well-defined because all H-coinvariant relations are G-coinvariant relations. Define τ([w]_G) = ∑_{s∈S}[sw]_H. Changing s to hs leaves the summand unchanged. For g ∈ G, right multiplication sends the right transversal S to the right transversal Sg. Independence of representatives therefore gives ∑_s[sgw]_H = ∑_s[sw]_H. The linear map from W given by this sum kills every gw − w and hence their k-span, so τ descends to W_G. Finally πτ([w]_G) = ∑_s[sw]_G = d[w]_G. Since every class has a representative, πτ = d id on all of W_G.

13. Apply step 12 in each degree to the diagonal G-representation W_n = A ⊗_k B(G)_n. Its differential is G-equivariant and k-linear, so it commutes both with π and with the finite sum defining τ. These are therefore chain maps whose composite is d id in each degree. Their induced maps on homology send a cycle class to the class of its image; these maps are well-defined because boundaries map to boundaries. Using step 9, they give H_n(G,A) → H_n(H,A) → H_n(G,A) with composite d id for every n ≥ 0.

14. In Tate degree zero, inclusion A^G → A^H descends to a map R₀ : A^G/im(ν_G) → A^H/im(ν_H). To verify this, use G = ⋃_{s∈S} Hs to obtain N_G(a) = ∑_{s,h} hsa = N_H(∑_s sa). Thus every element of im(ν_G), viewed as an H-invariant element, belongs to im(ν_H).

15. Define C₀ on an H-invariant representative a by the class of ∑_{t∈T}ta. Replacing t by th changes no summand because ha = a. Left multiplication by any g permutes the left cosets, so this sum is G-invariant. Moreover, for any b ∈ A, its value on N_H(b) is ∑_{t,h}thb = N_G(b), by the bijection T × H → G. Hence it sends im(ν_H) into im(ν_G) and descends to the desired quotient. If a is G-invariant, each ta equals a, so C₀R₀ sends its class to d times that class. Every class has an invariant representative, proving C₀R₀ = d id.

16. In Tate degree −1, use τ : A_G → A_H and π : A_H → A_G from step 12. They restrict to maps ker(ν_G) → ker(ν_H) and ker(ν_H) → ker(ν_G). For the first assertion, represent a coinvariant class by a. The underlying element of ν_H(τ([a]_G)) is ∑_{s,h}hsa = N_G(a). Thus ν_G([a]_G) = 0 implies ν_H(τ([a]_G)) = 0. For the second assertion, the underlying element of ν_G(π([a]_H)) is N_G(a) = ∑_{t∈T}tN_H(a). It is zero when ν_H([a]_H) = 0. These computations in A establish the equalities in the invariant submodules because their inclusions into A are injective. The identity πτ = d id restricts to the kernels as well, since equality there is detected by inclusion into A_G.

17. We now use the given vanishing hypothesis in the appropriate branch of the frozen Tate definition. If q ≥ 1, step 11 supplies maps through the zero module H^q(H,A). If q = 0, steps 14 and 15 supply maps through the zero quotient A^H/im(ν_H). If q = −1, step 16 supplies maps through the zero kernel ker(ν_H). If q ≤ −2, set n = −q−1 ≥ 1 and use step 13 through the zero module H_n(H,A). These cases exhaust the integers and agree exactly with the four branches of Rep.tateCohomology.

18. In each case the first map sends every element to zero, and the second sends zero to zero. Their composite is therefore zero. The same composite is d times the identity. All identifications used above are linear, so d times the identity acts by repeated addition on the underlying module. Thus H.index • x = 0 for every x : A.tateCohomology q, as required.

## Key steps

1. Convert the restricted zero-object hypothesis into elementwise vanishing and identify the four frozen Tate branches.
2. Choose left and right transversals, both of cardinality H.index.
3. Identify homogeneous cochains and diagonal tensor coinvariant chains with the defining inhomogeneous complexes.
4. Use an H-equivariant coset retraction and the explicit prism homotopy to compute the H groups with B(G).
5. Construct cohomological restriction and coset-sum corestriction; prove their composite is H.index times the identity.
6. Construct coinvariant transfer and projection, then apply them degreewise to obtain the homological index identity.
7. Establish the same index identity on the invariant/norm quotient and on the kernel of normBar.
8. Split into the four Tate degrees and use factorization through the zero restricted module to obtain index annihilation.

## Reference use

### local-project

Queries:
- `TateResCor|tateCohomology.*index|index.*tateCohomology`
- `transfer|corestriction|cores.*res|res.*cores`
- `inhomogeneousCochainsIso|inhomogeneousChainsIso|isZero_iff_subsingleton|theorem not_dvd_index|instance nonempty`
- `index_pos|card_mul_index|index_mul_card`
- `prime|nsmul|addOrderOf`
- `annihilat|forall.*Prime.*nsmul|nsmul.*prime|prime.*nsmul`
- `p04_index_nsmul_zero_of_restriction_isZero|p04_eq_zero_of_prime_avoiding_annihilators`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/project/Definitions/Def_GroupCohomology_TateCohomology.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/RepresentationTheory/Homological/GroupHomology/Functoriality.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Sylow.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/Index.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/mathlib/Mathlib/GroupTheory/OrderOfElement.lean`

Searched using /runtime/bin/rg. Verified clean snapshot HEADs at project 2475a3790d7ba0c3b10be8086001b154a45be597 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; all nine installed package revisions match the local Lake manifest and have clean source trees. The Tate definition supplies normBar and the four degree branches. The cohomology and homology Basic files supply the inhomogeneous-complex identifications, including the inverse action in the homology differential. ModuleCat.isZero_iff_subsingleton, Sylow.nonempty, Sylow.not_dvd_index, and subgroup index counting already exist. Homology Functoriality supplies corestriction, but the searches found no general Tate index-annihilation theorem or TateResCor declarations. OrderOfElement supplies additive-order infrastructure. The active DAG contains only the root; both proposed identifiers had no matches. Transitive #print axioms checks on the cited library declarations returned only propext, Classical.choice, and Quot.sound. Both proposed types elaborate against the exact contract imports; the first infers a single shared universe and natural-number scalar multiplication NSMul.toSMul. Evidence is in /tmp/p04-decomposition-6n0g0g_v/ImportContextTypeProbe.log. The stricter import Submission check is blocked: unchanged Submission.lean reports unknown constant Representation.TateResCor.cosetDecomp_apply at line 10. No frozen source was changed, and no proof acceptance is claimed.
