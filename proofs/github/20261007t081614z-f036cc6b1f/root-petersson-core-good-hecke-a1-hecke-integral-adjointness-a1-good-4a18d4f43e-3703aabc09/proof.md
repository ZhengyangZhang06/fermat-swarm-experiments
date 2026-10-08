# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1.unique_projective_index-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix p, a, b, v satisfying the hypotheses. Since p is prime, p ≥ 2 and F = ℤ/pℤ is a field. Write A, B, V for the reductions of a, b, v in F. Reduction of an integer is zero exactly when p divides that integer. Thus A and B are not both zero, and V ≠ 0.
2. Every i in Fin(p+1) has 0 ≤ i.val ≤ p. Consequently either i.val < p, or i.val = p and i = Fin.last p. In the first case the reduction of D(i) is B − A·[i.val]. In the second case it is A·V, because the reduction of b·p is zero.
3. Suppose A ≠ 0. Define x = B/A in F. Let j = x.val be its canonical natural representative. The residue-field representative identities give j < p and [j] = x. Let i₀ in Fin(p+1) have value j. Then A·[j] = B, so D(i₀) reduces to zero and p divides D(i₀).
4. Still assuming A ≠ 0, the last index cannot satisfy the divisibility condition: its reduced value is A·V, which is nonzero since both factors are nonzero in a field.
5. If another index i satisfies the condition, step 4 implies i.val < p. Step 2 gives A·[i.val] = B = A·[j]. Cancel A to obtain [i.val] = [j]. Taking canonical natural representatives gives i.val = j, since both values are less than p. Equality of Fin elements follows from equality of their values, so i = i₀. This proves existence and uniqueness when A ≠ 0.
6. Suppose instead A = 0. The hypothesis that A and B are not both zero implies B ≠ 0. For every index with value less than p, step 2 now gives the nonzero reduced value B. None of these indices satisfies the divisibility condition. At Fin.last p the reduced value is A·V = 0, so this index does satisfy it. Every index is covered by the alternatives in step 2; therefore the last index is the unique solution.
7. The two cases A ≠ 0 and A = 0 exhaust all possibilities and establish the asserted unique index.

## Key steps

1. Translate integer divisibility into vanishing in the field ZMod p.
2. Separate the indices with value less than p from the unique last index.
3. When the first coordinate is nonzero, choose the canonical representative of B/A.
4. Exclude the last index and prove uniqueness by cancellation and canonical representatives.
5. When the first coordinate vanishes, use the nonzero second coordinate to show that exactly the last index works.

## Reference use

### local-project

Queries:
- `def heckeMatrix|def heckeDiagMatrix|heckeMatrix.*coe|coe.*heckeMatrix|heckeDiagMatrix.*coe|coe.*heckeDiagMatrix|exists.*[Bb]ezout|transversal`
- `mapGL|coe_inv|coe_mul|det_coe|det_eq|def mk|fin_two`
- `intCast_zmod_eq_zero|val_lt|val_injective|intCast_zmod_cast|cast_val`
- `transversal|[Bb]ezout.*hecke|hecke.*[Bb]ezout|projective.*index`
- `f036cc6b1f_pc_hi_gpt_(unique_projective_index|bezout_lift)`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --short`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/f036cc6b1f_gpt_split_23h6rj5x/Types.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperator.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Data/ZMod/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Data/Int/GCD.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Data/Nat/Prime/Defs.lean`
- `/tmp/f036cc6b1f_gpt_split_23h6rj5x/Types.lean`
- `/tmp/f036cc6b1f_gpt_split_23h6rj5x/Types.log`
- `/tmp/f036cc6b1f_gpt_split_23h6rj5x/Compatibility.json`
- `/tmp/f036cc6b1f_gpt_split_23h6rj5x/check-command.json`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected sources supply the exact Hecke matrix values, Gamma0 membership criterion, SL2 inverse formula, canonical real embedding, Bézout identity, and residue/divisibility and representative lemmas. The project search found no matching transversal or Bézout–Hecke helper; neither proposed identifier occurs in the searched DAG metadata. Both literal child propositions elaborated successfully after import Submission. Fully explicit elaboration confirmed Units.instMul over Matrix.semiring and the canonical integer-to-real algebra instance. Installed mathlib is clean at the pinned revision, and all 20 imported project sources in the selected offline cache match the snapshot. Transitive axiom checks of the cited supporting declarations returned only subsets of propext, Classical.choice, and Quot.sound. These checks validate the proposed interfaces and library references; they do not constitute comparator acceptance of child proofs.
