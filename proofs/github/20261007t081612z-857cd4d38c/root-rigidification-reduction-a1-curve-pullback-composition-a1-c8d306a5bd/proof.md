# Parent-supplied natural-language proof

- Parent DAG node: `root.rigidification_reduction-a1`
- Child DAG node: `root.rigidification_reduction-a1.curve_pullback_composition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write α = Spec(f) and β = Spec(h). Unpack the two IsPullbackVia hypotheses into their pullback squares and their multiplication, action, and level conditions. Their commuting equations are g₀₁ ≫ E₀.f = E₁.f ≫ α and g₁₂ ≫ E₁.f = E₂.f ≫ β. Hence (g₁₂ ≫ g₀₁) ≫ E₀.f = E₂.f ≫ (β ≫ α). Contravariance of Spec identifies β ≫ α with Spec(h.comp f).
2. Verify the universal property of this composite square. Given any scheme X, maps a : X → E₀.A and t : X → Spec S₂ satisfying a ≫ E₀.f = t ≫ β ≫ α, the first pullback square gives a unique b : X → E₁.A with b ≫ g₀₁ = a and b ≫ E₁.f = t ≫ β. The second gives a unique c : X → E₂.A with c ≫ g₁₂ = b and c ≫ E₂.f = t. Then c ≫ g₁₂ ≫ g₀₁ = a. If c' satisfies the same outer equations, c' ≫ g₁₂ has the two defining equations of b and therefore equals b; uniqueness in the second square now gives c' = c. Thus the composite square is a pullback.
3. Fix X, t : X → Spec S₂, and E₂-points P,Q over t. Let P₁,Q₁ be their composites with g₁₂, regarded as E₁-points over t ≫ β using the second square's commuting equation. Let P₀,Q₀ be their further composites with g₀₁, now over t ≫ β ≫ α. The second multiplication condition gives (E₂.L.mul t P Q).1 ≫ g₁₂ = (E₁.L.mul (t ≫ β) P₁ Q₁).1. Composing this equality with g₀₁ and applying the first multiplication condition gives (E₂.L.mul t P Q).1 ≫ (g₁₂ ≫ g₀₁) = (E₀.L.mul (t ≫ Spec(h.comp f)) P₀ Q₀).1. Associativity and Spec's composition identity identify the displayed bases and the point morphisms with those required by the composite predicate; proof irrelevance identifies their over-base proofs.
4. For each x ∈ Λ, the two action conditions give E₂.act(x) ≫ g₁₂ ≫ g₀₁ = g₁₂ ≫ E₁.act(x) ≫ g₀₁ = g₁₂ ≫ g₀₁ ≫ E₀.act(x). This is the composite action condition.
5. Suppose a point P of E₂ over t factors through E₂.lev. The second level condition supplies w₁ : X → E₁.C with w₁ ≫ E₁.lev = P.1 ≫ g₁₂. Thus P₁ factors through E₁.lev. Applying the first level condition to P₁ supplies w₀ : X → E₀.C with w₀ ≫ E₀.lev = P₁.1 ≫ g₀₁ = P.1 ≫ (g₁₂ ≫ g₀₁). This is exactly the required final level witness.
6. The pullback square from step 2 together with steps 3–5 supplies every conjunct of IsPullbackVia (h.comp f) E₀ E₂ (g₁₂ ≫ g₀₁).

## Key steps

1. Identify the composite base morphism using contravariance of Spec.
2. Construct and prove uniqueness of the outer lift by two successive pullback lifts.
3. Compose multiplication compatibility on test-scheme points.
4. Compose action compatibility by associativity.
5. Pass level-factorization witnesses through both morphisms.
6. Assemble the composite IsPullbackVia predicate.

## Reference use

### local-project

Queries:
- `rg -n 'structure Rigidification|def IsPullbackVia|structure IsPullbackVia|def IsIsogenyPair|structure IsIsogenyPair|preservesLevel|namespace Rigidification' .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions`
- `rg -n 'IsPullbackVia|IsIsogenyPair' .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Theorems --glob '*.lean'`
- `rg -n 'paste_horiz|paste_vert|theorem.*comp|def mapPt|def FactorsThrough' .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `rg -n --hidden --no-ignore 'p07_rr_pullback_comp_857cd4d38c|p07_rr_isogeny_transport_857cd4d38c' /mnt/data/zhengyang-workspace/fermat-swarm-projects --glob 'dag.json' --glob '*handoff*.json' --glob '*.lean'`
- `#print axioms CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia`
- `#print axioms CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair`
- `#print axioms CerednikDrinfeld.QM.FakeEllipticCurve.PreservesLevel`
- `#print axioms CerednikDrinfeld.QM.mapPt`
- `#print axioms CerednikDrinfeld.QM.FactorsThrough`
- `#print axioms CategoryTheory.IsPullback.paste_horiz`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMIsogeny.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMRigidification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Theorems`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/tmp/p07-rr-decomposition-857cd4d38c/TypesAgainstImports.lean`
- `/tmp/p07-rr-decomposition-857cd4d38c/types-and-axioms.log`
- `/tmp/p07-rr-decomposition-857cd4d38c/literal-submission.log`
- `/tmp/p07-rr-decomposition-857cd4d38c/literal-import.log`

The manifest pins project 73257f1e32d99b75813b037f28a5cf45a2db886d and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; the checked revisions match and their checked tracked sources are clean. All 47 project modules in the import closure match the snapshot and the cached source modules used for diagnostics. IsPullbackVia contains a pullback square, multiplication compatibility, action compatibility, and directional level preservation. IsIsogenyPair and PreservesLevel have exactly the conditions addressed below. Mathlib supplies IsPullback.paste_horiz. The searched project Theorems directory contains no IsPullbackVia or IsIsogenyPair matches, and the proposed-name search found no collisions. Both proposed types elaborate against Submission's five imports under Lean 4.33.1. The six audited declarations depend only on propext, Classical.choice and Quot.sound. Literal import Submission remains blocked: unchanged Submission.lean reports unknown attribute targets AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase and RegularLocalRingQuotientAscent.dualNumberFst_apply, so no importable Submission object is produced. These diagnostic checks are not comparator acceptance.
