# fermat-p02

Local repository problem, not a Lean-Eval acquisition.

Repository: ZhengyangZhang06/fermat-swarm-experiments

Source revision: `1f74c284b125d4c45f527f2d621597fcf1e103a9`

Frozen source: `Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean`

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HeckeEis_eichlerShimuraMap_injective.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_injective (N : ℕ) [NeZero N] (n : ℕ) :
    Function.Injective
      (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f) := by
  sorry
```

The source is an unsolved specification. Preserve all binders, assumptions, definitions and the conclusion. A missing proof or sorry is not a solution. Use no network search. Every new named helper must have its own theorem node, issue, prose proof, Lean proof and verified solution PR.
