<!-- theorem-id: fermat-p04/root.prime_avoiding_annihilators-a1 -->

## Theorem `Submission.p04_eq_zero_of_prime_avoiding_annihilators`

Let V be an additive abelian group. Suppose that for every prime natural number p there exists a natural number m such that m > 0, p does not divide m, and m • v = 0 for every v in V. Then every element of V equals zero. No finiteness assumption on V is required.

Node: `root.prime_avoiding_annihilators-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/4

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p04_eq_zero_of_prime_avoiding_annihilators`

```lean
∀ {V : Type*} [AddCommGroup V], (∀ p : ℕ, p.Prime → ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ v : V, m • v = 0) → ∀ v : V, v = 0
```

### Frozen project context

`Fermat/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean` at `2475a3790d7ba0c3b10be8086001b154a45be597` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
attribute [-simp] Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.prime_avoiding_annihilators-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix an additive abelian group V satisfying the hypothesis, and fix v ∈ V. Since 2 is prime, the hypothesis supplies a positive natural number m₂ with m₂ • w = 0 for every w ∈ V. In particular m₂ • v = 0.

2. Therefore the set of positive natural numbers n satisfying n • v = 0 is nonempty. By well-ordering, choose its least element n. Then n > 0, n • v = 0, and any positive natural number annihilating v is at least n.

3. Let m be any natural number with m • v = 0; positivity of m is not needed here. Euclidean division by the positive n gives m = an + r with 0 ≤ r < n. The laws of repeated addition give m • v = a • (n • v) + r • v = r • v. Hence r • v = 0. If r > 0, minimality would give n ≤ r, contradicting r < n. Thus r = 0, and n divides m.

4. Suppose n > 1. Among the divisors of n greater than 1 choose the least, denoted p; such a divisor exists because n divides itself. Then p is prime. Indeed p > 1, and if a positive divisor a of p satisfied 1 < a < p, transitivity of divisibility would make a a divisor of n greater than 1, contradicting the choice of p. Thus the only positive divisors of p are 1 and p, which proves primality.

5. Apply the hypothesis to this prime p. Obtain a positive natural number m such that p does not divide m and m • w = 0 for every w ∈ V. In particular m • v = 0, so step 3 gives n ∣ m. Since p ∣ n by construction, transitivity yields p ∣ m, contradicting the choice of m.

6. Therefore n is not greater than 1. Since n is positive, n = 1. The equality n • v = 0 now reads 1 • v = 0, and 1 • v = v, so v = 0. The element v was arbitrary, proving the stated conclusion.

## Key steps

1. Use the prime 2 to obtain a positive annihilator of a fixed element.
2. Choose its least positive annihilator n.
3. Use Euclidean division and minimality to show that n divides every annihilator of that element.
4. If n exceeds 1, choose a prime divisor p and contradict the existence of a p-avoiding annihilator.
5. Conclude n = 1 and hence that the element is zero.

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


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/523

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
