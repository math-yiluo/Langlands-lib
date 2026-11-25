/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `rfl_by_kernel`

`rfl_by_kernel` closes a goal `l = r` by `Eq.refl l`, without asking the elaborator to check that
`l` and `r` are definitionally equal: the check is left to the kernel, which performs it when the
declaration is added. It is the analogue of `exact_by_kernel` for reflexivity.

This is meant for equations whose two sides agree up to the spelling of objects and categories
inside large composites (for instance two definitionally equal presentations of the same
derived functors), on which the elaborator's unifier unfolds instances eagerly and runs out of
heartbeats. If the two sides are not definitionally equal, the kernel rejects the declaration.
-/

public meta section

namespace RflByKernel

open Lean Meta Elab Tactic

/-- `rfl_by_kernel` closes a goal `l = r` by `Eq.refl l`, leaving the definitional equality of
`l` and `r` to the kernel. -/
elab "rfl_by_kernel" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, lhs, _) := (← whnfR (← instantiateMVars (← g.getType))).eq?
    | throwError "rfl_by_kernel: the goal is not an equation"
  g.assign (← mkEqRefl lhs)
  replaceMainGoal []

end RflByKernel
