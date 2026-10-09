# Dominant-term nonvanishing: internal milestone

`internal_milestone_complete: true`

`selected_node_complete: false`

This local result implements the unique-dominant-term nonvanishing sentence in accepted-proof step 2 for `Submission.p03_tate_uniformization_68cf3476`. It does not complete that selected theorem. No issue, helper node, solution declaration, candidate theorem commit, publication, controller transition, or comparator run is represented by this note. The original theorem's clean-commit, exact-contract-comparator, transitive-axiom and independent-review gates remain required.

The numbered proof, exact anonymous Lean sources, paste-ready local block, compiler configuration and full validation logs are archived at `.humanize/recovery/20261008T235754Z-dominant-term/`. This directory is ignored; this proof note is the permitted durable commit artifact. No ignored diagnostics were force-added.

## Argument

All claims below are local steps, with no new named solution declarations.

1. Fix a normed field K with the stated ultrametric inequality. If x,y : K satisfy ‖y‖ < ‖x‖, then ‖x+y‖ ≤ ‖x‖. Applying the inequality to (x+y)+(-y)=x gives ‖x‖ ≤ max(‖x+y‖,‖y‖). The second argument is strictly less than ‖x‖, so ‖x‖ ≤ ‖x+y‖. Hence ‖x+y‖ = ‖x‖.
2. Fix a : ℤ → K and m : ℤ with a m ≠ 0 and every other term strictly smaller in norm. Put R=‖a m‖>0. For each finite s not containing m, prove ‖∑ n∈s, a n‖ < R by induction: the empty sum has norm 0<R; insertion uses the ultrametric inequality and max of two strictly smaller real numbers.
3. For every finite s containing m, s.erase m excludes m. By step 2 its sum has norm <R. By step 1, a m plus that sum has norm R; this is exactly the sum over s.
4. Assume Summable a. Its finite partial sums converge to ∑' n, a n by Summable.hasSum. Continuity of norm implies convergence of their norms to the norm of that sum. Eventually the finite sets contain m (they contain the singleton {m}), so their norms are eventually the constant R. Uniqueness of limits in ℝ gives ‖∑' n, a n‖=R. Since R>0, the sum is nonzero. No completeness or uniform strict gap for the whole tail is needed.
5. For any c : ℤ → K and u : Kˣ, substitute a n=c n*(u:K)^n. The only assumptions are summability, a nonzero m-th term, and strict dominance over n≠m. This proves the Laurent specialization and implements the unique-maximizer nonvanishing sentence in accepted-proof step 2, once those assumptions have been established at the chosen u. It does not establish convergence, existence of a maximizer, or annular zero counting.

No mathematical step remains unsupported for this internal proposition. Formal API checks follow.

## Exact anonymous generic source

```lean
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

example :
    ∀ (K : Type) [NormedField K],
      (∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖) →
      ∀ a : ℤ → K, Summable a → ∀ m : ℤ,
        a m ≠ 0 →
        (∀ n : ℤ, n ≠ m → ‖a n‖ < ‖a m‖) →
        ‖∑' n : ℤ, a n‖ = ‖a m‖ ∧ (∑' n : ℤ, a n) ≠ 0 := by
  intro K _ hna a ha m hm hdom
  classical
  have hadd (x y : K) (hxy : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
    apply le_antisymm
    · exact (hna x y).trans (max_le le_rfl hxy.le)
    · have hrev : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
        simpa only [add_neg_cancel_right, norm_neg] using hna (x + y) (-y)
      exact (le_max_iff.mp hrev).resolve_right (not_le.mpr hxy)
  have hsmall (s : Finset ℤ) (hms : m ∉ s) : ‖∑ n ∈ s, a n‖ < ‖a m‖ := by
    induction s using Finset.induction_on with
    | empty => simpa using norm_pos_iff.mpr hm
    | @insert n s hns ih =>
      have hmn : m ≠ n := fun h => hms (h ▸ Finset.mem_insert_self n s)
      have hmt : m ∉ s := fun h => hms (Finset.mem_insert_of_mem h)
      rw [Finset.sum_insert hns]
      exact (hna _ _).trans_lt (max_lt (hdom n hmn.symm) (ih hmt))
  have hfinite (s : Finset ℤ) (hms : m ∈ s) : ‖∑ n ∈ s, a n‖ = ‖a m‖ := by
    rw [← Finset.add_sum_erase s a hms]
    exact hadd _ _ (hsmall (s.erase m) (by simp))
  have hevent : Filter.EventuallyEq Filter.atTop
      (fun s : Finset ℤ => ‖∑ n ∈ s, a n‖) (fun _ => ‖a m‖) := by
    filter_upwards [Filter.eventually_ge_atTop ({m} : Finset ℤ)] with s hs
    exact hfinite s (hs (Finset.mem_singleton_self m))
  have hnorm : ‖∑' n : ℤ, a n‖ = ‖a m‖ := by
    have ht := (show Filter.Tendsto (fun s : Finset ℤ => ∑ n ∈ s, a n)
      Filter.atTop (nhds (∑' n : ℤ, a n)) from ha.hasSum).norm
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hevent.symm)
  refine ⟨hnorm, ?_⟩
  exact norm_pos_iff.mp (hnorm.symm ▸ norm_pos_iff.mpr hm)
```

## Exact anonymous Laurent specialization

```lean
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

example :
    ∀ (K : Type) [NormedField K],
      (∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖) →
      ∀ (c : ℤ → K) (u : Kˣ),
        Summable (fun n : ℤ => c n * (u : K) ^ n) → ∀ m : ℤ,
        c m * (u : K) ^ m ≠ 0 →
        (∀ n : ℤ, n ≠ m → ‖c n * (u : K) ^ n‖ < ‖c m * (u : K) ^ m‖) →
        ‖∑' n : ℤ, c n * (u : K) ^ n‖ = ‖c m * (u : K) ^ m‖ ∧
          (∑' n : ℤ, c n * (u : K) ^ n) ≠ 0 := by
  have hdominant :
      ∀ (K : Type) [NormedField K],
        (∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖) →
        ∀ a : ℤ → K, Summable a → ∀ m : ℤ,
          a m ≠ 0 →
          (∀ n : ℤ, n ≠ m → ‖a n‖ < ‖a m‖) →
          ‖∑' n : ℤ, a n‖ = ‖a m‖ ∧ (∑' n : ℤ, a n) ≠ 0 := by
    intro K _ hna a ha m hm hdom
    classical
    have hadd (x y : K) (hxy : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
      apply le_antisymm
      · exact (hna x y).trans (max_le le_rfl hxy.le)
      · have hrev : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
          simpa only [add_neg_cancel_right, norm_neg] using hna (x + y) (-y)
        exact (le_max_iff.mp hrev).resolve_right (not_le.mpr hxy)
    have hsmall (s : Finset ℤ) (hms : m ∉ s) : ‖∑ n ∈ s, a n‖ < ‖a m‖ := by
      induction s using Finset.induction_on with
      | empty => simpa using norm_pos_iff.mpr hm
      | @insert n s hns ih =>
        have hmn : m ≠ n := fun h => hms (h ▸ Finset.mem_insert_self n s)
        have hmt : m ∉ s := fun h => hms (Finset.mem_insert_of_mem h)
        rw [Finset.sum_insert hns]
        exact (hna _ _).trans_lt (max_lt (hdom n hmn.symm) (ih hmt))
    have hfinite (s : Finset ℤ) (hms : m ∈ s) : ‖∑ n ∈ s, a n‖ = ‖a m‖ := by
      rw [← Finset.add_sum_erase s a hms]
      exact hadd _ _ (hsmall (s.erase m) (by simp))
    have hevent : Filter.EventuallyEq Filter.atTop
        (fun s : Finset ℤ => ‖∑ n ∈ s, a n‖) (fun _ => ‖a m‖) := by
      filter_upwards [Filter.eventually_ge_atTop ({m} : Finset ℤ)] with s hs
      exact hfinite s (hs (Finset.mem_singleton_self m))
    have hnorm : ‖∑' n : ℤ, a n‖ = ‖a m‖ := by
      have ht := (show Filter.Tendsto (fun s : Finset ℤ => ∑ n ∈ s, a n)
        Filter.atTop (nhds (∑' n : ℤ, a n)) from ha.hasSum).norm
      exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hevent.symm)
    refine ⟨hnorm, ?_⟩
    exact norm_pos_iff.mp (hnorm.symm ▸ norm_pos_iff.mpr hm)
  intro K _ hna c u hs m hm hdom
  exact hdominant K hna (fun n : ℤ => c n * (u : K) ^ n) hs m hm hdom
```

## Paste-ready local block

```lean
have hdominant :
    ∀ (K : Type) [NormedField K],
      (∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖) →
      ∀ a : ℤ → K, Summable a → ∀ m : ℤ,
        a m ≠ 0 →
        (∀ n : ℤ, n ≠ m → ‖a n‖ < ‖a m‖) →
        ‖∑' n : ℤ, a n‖ = ‖a m‖ ∧ (∑' n : ℤ, a n) ≠ 0 := by
  intro K _ hna a ha m hm hdom
  classical
  have hadd (x y : K) (hxy : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
    apply le_antisymm
    · exact (hna x y).trans (max_le le_rfl hxy.le)
    · have hrev : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
        simpa only [add_neg_cancel_right, norm_neg] using hna (x + y) (-y)
      exact (le_max_iff.mp hrev).resolve_right (not_le.mpr hxy)
  have hsmall (s : Finset ℤ) (hms : m ∉ s) : ‖∑ n ∈ s, a n‖ < ‖a m‖ := by
    induction s using Finset.induction_on with
    | empty => simpa using norm_pos_iff.mpr hm
    | @insert n s hns ih =>
      have hmn : m ≠ n := fun h => hms (h ▸ Finset.mem_insert_self n s)
      have hmt : m ∉ s := fun h => hms (Finset.mem_insert_of_mem h)
      rw [Finset.sum_insert hns]
      exact (hna _ _).trans_lt (max_lt (hdom n hmn.symm) (ih hmt))
  have hfinite (s : Finset ℤ) (hms : m ∈ s) : ‖∑ n ∈ s, a n‖ = ‖a m‖ := by
    rw [← Finset.add_sum_erase s a hms]
    exact hadd _ _ (hsmall (s.erase m) (by simp))
  have hevent : Filter.EventuallyEq Filter.atTop
      (fun s : Finset ℤ => ‖∑ n ∈ s, a n‖) (fun _ => ‖a m‖) := by
    filter_upwards [Filter.eventually_ge_atTop ({m} : Finset ℤ)] with s hs
    exact hfinite s (hs (Finset.mem_singleton_self m))
  have hnorm : ‖∑' n : ℤ, a n‖ = ‖a m‖ := by
    have ht := (show Filter.Tendsto (fun s : Finset ℤ => ∑ n ∈ s, a n)
      Filter.atTop (nhds (∑' n : ℤ, a n)) from ha.hasSum).norm
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hevent.symm)
  refine ⟨hnorm, ?_⟩
  exact norm_pos_iff.mp (hnorm.symm ▸ norm_pos_iff.mpr hm)
```

## Application

Paste `LocalHave.lean.txt` as a local `have hdominant` into the selected proof's tactic block. It introduces no global declaration. `FrozenImportsCheck.lean.txt` checks that exact block under the two unchanged import declarations used by Submission, without importing Submission or its root placeholder. It requires no additional `open` commands.

At a fixed unit u, put a n = c n * (u : K)^n. Once summability, nonzero leading term at m, and strict norm dominance over every n ≠ m are available, use:

```lean
obtain ⟨hnorm, hne⟩ :=
  hdominant K hna (fun n : ℤ => c n * (u : K) ^ n) hs m hm hdom
```

Here `hna` is the ultrametric inequality in K; `hs`, `hm`, and `hdom` are exactly the three hypotheses in the Laurent example. In accepted-proof step 2 take K = Ω and embed coefficients from the finite field E into Ω when necessary. Then hne proves f(u) ≠ 0 for a unique maximizing term. The norm equality also identifies |f(u)| with the dominant term's norm.

This supplies exactly the sentence “A unique maximizing term precludes a zero.” Convergence, existence of a maximizing index, movement of maxima, tie-radius behavior, and annular zero counting remain separate obligations. No completeness, discreteness, algebraic closedness, zero-counting assumption, or prior bound on the total sum is added here.

Status: internal_milestone_complete: true; selected_node_complete: false. These checks do not constitute selected-theorem or root acceptance, and no comparator was run.

## Validation evidence

Six final warning-fatal Lean checks exited zero: the two anonymous examples, the exact local-have wrapper, the three-body private axiom probe, and anonymous/private-probe wrappers using the two frozen import declarations. The first four do not load any project theorem. The frozen-import wrappers load the existing private Definitions artifacts, with their hashes recorded; neither imports Submission or AcceptedDependencies. No root placeholder is used.

All four printed transitive-axiom sets are exactly `[propext, Classical.choice, Quot.sound]`. The generic statement matches the supplied contract after whitespace normalization; the private probes reuse the exact proof bodies. The local block is embedded byte-for-byte in both its wrapper and the Laurent specialization. Source scanning found no placeholders, new solution declarations, new axioms, or unsafe mechanisms.

The separate requested code simplifier reviewed the final source hashes and numbered prose, found no issue, and recommended retaining the proof. This review is internal and does not constitute selected-node acceptance. Outside RLCR verification remains pending.

Compiler: Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Flags:

```text
-DwarningAsError=true
-DautoImplicit=false
-DmaxHeartbeats=4000000
-DsynthInstance.maxHeartbeats=400000
-Dbackward.isDefEq.respectTransparency.types=false
```

Pinned project: `81f093181fd6c58dc887fcae5ec8b896996f1885`. Pinned mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`. Both local snapshots and all nine compiler-package repositories matched their recorded commits and had empty full Git status. No acquisition or network search occurred.

The initial Lean attempt failed only on the obsolete spelling `Finset.not_mem_erase`; the pinned simp theorem is `Finset.notMem_erase`, used through `by simp`. Full initial and final sources/logs are retained. No compiler-header repair was required.

## Scope and external-state observation

All 240 monitored files other than the shared external DAG were byte-identical at final inspection, including tracked inputs, Submission, frozen problem/proof/plan records, the stopped loop, and this loop's controller state. This work did not edit controller files. The shared DAG's digest nevertheless changed externally during execution:

```text
before: f38b92e279002cc660be5c9a2670401b3a0ea546f0df43d5f84ff4826d9c8ab2
first observed after: 76c86e7dfb48cfef495393ca7e47e8a204fae48b731c44847aeecbcdea42ec81
```

The DAG continued to change on subsequent reads; these are point-in-time hashes, not a claim of stable external state. Its cause and semantic delta were not established. This is queued for outside review (analyze / codex); no restoration, takeover, or controller action was attempted. The independent proposition and its checks have no DAG dependency, so it does not block this internal milestone. This note does not claim that the shared DAG remained byte-identical.

Full annular zero counting, the four remaining selected-theorem obligations, old comparator provenance, assembly optimization, publication and final selected-node acceptance remain outside this round.

## Archived source hashes

| Source | SHA-256 |
| --- | --- |
| DominantTerm.lean.txt | `d913dc9207c1461d23879be604b1e1f21c9a387528b197d3dd0ac9bbf7773c46` |
| LaurentSpecialization.lean.txt | `0c95cdc206547656b10cea522d9c9e55497b4906dd25ffdc64e9052efce050ae` |
| LocalHave.lean.txt | `c73e20ac56a831c66a6fc9c8cbe51d7e7139ac98c7e2944f9efa71decbbcbdcc` |

Archive `SHA256SUMS` digest: `3540947216c620e684ffc0a4a2baa73db4250adc84d2eb1984b1511ef653f476`. It covers the exact sources, full logs, settings, replay instructions, compatibility evidence, safety audit, scope audit and simplifier review.

Round tracker digest: `96248b3d5885bdcfaa6b74ef203413dfa4a9b9e190f9529c67a57fe6d73ed78d`. Round contract digest: `fd9d12c067e8850953dbd2fd2f523b581311d55136b2e6a1c1282637711e1610`.
