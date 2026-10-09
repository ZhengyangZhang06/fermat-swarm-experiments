# Final proof of `Rep.isZero_tateCohomology_of_forall_sylow`

## Statement and assumptions

Let `k` and `G` have the same arbitrary universe `u`. Assume `[CommRing k]`,
`[Group G]`, and `[Fintype G]`. Let `A : Rep.{u} k G` and `q : ℤ`. Assume

```lean
h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
  CategoryTheory.Limits.IsZero
    ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)
```

Then `CategoryTheory.Limits.IsZero (A.tateCohomology q)`.
There is no normality assumption on the Sylow subgroups, no finiteness or
projectivity assumption on `A`, and no restriction on the integer degree.
The ring need not be a field or have specified characteristic.

## Accepted dependencies actually used by the root

1. `Submission.p04_index_nsmul_zero_of_restriction_isZero`, accepted candidate
   `100a5f6431970924f6f5e939cd799591c35d69ee`: for any commutative ring `k`, finite
   group `G`, representation `A : Rep k G`, subgroup `H : Subgroup G` equipped
   with `[Fintype H]`, and integer `q`,
   `IsZero ((Rep.res H.subtype A).tateCohomology q)` implies
   `∀ x : A.tateCohomology q, H.index • x = 0`.
2. `Submission.p04_eq_zero_of_prime_avoiding_annihilators`, accepted candidate
   `6d94ada56f3b333d660fa4207e7f2cbc365d8c8f`: for any additive commutative group
   `V`, if each prime natural number `p` admits a natural number `m` with
   `0 < m`, `¬ p ∣ m`, and `∀ v : V, m • v = 0`, then every `v : V` equals zero.

These are already proved dependency nodes, not additional assumptions of the
root theorem. Their statements and proof bodies are retained verbatim from
their accepted candidates. The index lemma uses the four degree branches of
the frozen Tate definition and the accepted transfer lemmas. The arithmetic
lemma uses a least positive annihilator: it exists by applying its hypothesis
at prime 2; division with remainder proves it divides every annihilator; any
prime divisor of a least annihilator different from 1 contradicts that prime's
avoiding annihilator. Thus the least annihilator is 1.

## Complete root argument

1. Put `V = A.tateCohomology q`. This is an object of `ModuleCat k`, so its
   underlying type has an additive commutative group structure. To prove it
   is a zero object it suffices to prove that every element is zero. The Lean
   proof first constructs `hzero : ∀ x : V, x = 0`.
2. Apply the accepted arithmetic lemma to this additive group. Fix an arbitrary
   `p : ℕ` and proof `hp : p.Prime`. Install the local instance
   `Fact p.Prime` with witness `hp`, exactly as required by `h` and the Sylow
   index theorem.
3. The pinned library supplies `Sylow.nonempty`. Use classical choice to choose
   `P : Sylow p G`. As a subgroup of finite `G`, its underlying type is finite;
   `Fintype.ofFinite (P : Subgroup G)` equips it with the finite enumeration
   required by the accepted index lemma and the hypothesis `h`.
4. Take `m = (P : Subgroup G).index`. The quotient `G ⧸ P` is finite because
   `G` is finite and is nonempty because it contains the identity coset.
   `Subgroup.index_ne_zero_of_finite` says its index is nonzero, and
   `Nat.pos_of_ne_zero` gives `0 < m`. The library instance
   `Subgroup.finiteIndex_of_finite` supplies the finite-index premise of
   `Sylow.not_dvd_index`, which gives `¬ p ∣ m`.
5. The hypothesis `h p P`, using precisely the local prime and subgroup
   finite-type instances just installed, says the restricted Tate module is
   a zero object. Apply
   `Submission.p04_index_nsmul_zero_of_restriction_isZero A (P : Subgroup G) q`
   to this proof. It gives `∀ x : V, m • x = 0`. Thus this same `m` satisfies
   all three requirements of the arithmetic lemma for the arbitrary prime
   `p`. No claim that all primes divide `|G|` is needed.
6. The arithmetic lemma therefore proves `hzero`. For any `x y : V`, the
   equalities `hzero x : x = 0` and `hzero y : y = 0` give `x = y` by
   transitivity with the second equality reversed. This constructs
   `Subsingleton V`.
7. Apply `ModuleCat.isZero_iff_subsingleton.mpr` to obtain the required
   `CategoryTheory.Limits.IsZero (A.tateCohomology q)`. Mathematically, when
   every element is zero, all linear maps into or out of the module are the
   zero map (maps out preserve zero, and maps in have only zero values),
   giving both universal properties of a zero object. This completes the
   conclusion with exactly the frozen hypotheses.

## Library provenance and historical decomposition

All library facts below come from the required local-project snapshot at
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8`.
Its project revision is `2475a3790d7ba0c3b10be8086001b154a45be597`; its mathlib
revision is `db584cd6d46c92f209a44c0f1c829460d327499d`. They are existing pinned
declarations, not new helper theorems:

- `mathlib/Mathlib/GroupTheory/Sylow.lean:213,489`: `Sylow.nonempty` and
  `Sylow.not_dvd_index`, respectively, provide existence and prime avoidance.
- `mathlib/Mathlib/GroupTheory/Index.lean:528,728`:
  `Subgroup.index_ne_zero_of_finite` and `Subgroup.finiteIndex_of_finite`
  justify positivity and the finite-index instance used above.
- `mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean:381`:
  `ModuleCat.isZero_iff_subsingleton` supplies the final categorical conclusion.
- `project/Definitions/Def_GroupCohomology_TateCohomology.lean:140` defines
  the module in all integer degrees. The root never changes or unfolds that
  definition; its accepted index dependency handles those degree cases.
- `Classical.choice`, `Fintype.ofFinite`, and `Nat.pos_of_ne_zero` are
  existing foundational/library operations supplied by the frozen imports.

The accepted natural proof `nodes/root/natural-proof-v4.md` and the older
`plan-draft-v1.md` remain unchanged history. The root's direct formal argument
is precisely steps 31–32 of that accepted proof, using the selected two
dependencies. The original proof's constructions of cohomological and
homological transfer, norm kernels/cokernels, and prism homotopies are
implemented by the already accepted descendant declarations; they are not
new obligations or additional root interfaces. The homological comparison
descendant uses the pinned projective-resolution infrastructure, as recorded
in that accepted proof's own source comments. The root requires only its
accepted conclusion, not a new reimplementation of that comparison.

All 22 accepted descendant declarations are preserved under their exact
globally qualified names, including the prism construction descendants.
`verification/root-overlay-preservation.json` records their frozen types,
accepted candidate commits, and hashes of their exact declaration bodies.
The inherited overlay contained duplicates, root placeholders, an unfinished
namespace block, and a detached root proof. Reconciliation retains one exact
accepted body per child in dependency order and places the root afterward.
The original `Representation` and `MonoidalCategory` namespace openings are
retained locally where the accepted child bodies need their names or notation.
No additional named theorem is introduced.

The frozen Git contract and its header are the source authority. Submission's
inherited missing negative-attribute line is restored to those frozen bytes.
Only private compiler copies may omit the single line authorized by operator
policy SHA256 `96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96`.
This compiler-input policy is independent of the mathematical argument and
does not itself certify any proof. Compilation compatibility, kernel axioms,
and exact-contract acceptance are determined by the configured comparator;
independent final-prose review remains the outer controller's responsibility.
