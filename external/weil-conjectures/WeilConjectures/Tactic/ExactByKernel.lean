/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `exact_by_kernel`

`exact_by_kernel h` closes the goal with the term `h`, without asking the elaborator to check that
the type of `h` is definitionally equal to the goal: the check is left to the kernel, which
performs it when the declaration is added.

This is meant for goals whose statement and the type of `h` agree up to the spelling of objects
and categories (for instance a category given as a projection of a structure, against its
value), inside large composites of derived functors. On such terms the elaborator's unifier
eagerly reduces projections of instances and runs out of heartbeats, even when the two types are
equal up to a few reductions which the kernel performs immediately. If the two types are not
definitionally equal, the kernel rejects the declaration.
-/

public meta section

namespace ExactByKernel

open Lean Meta Elab Tactic

/-- `exact_by_kernel h` closes the goal with `h`, leaving the definitional equality of the type of
`h` with the goal to the kernel. -/
elab "exact_by_kernel " h:term : tactic => withMainContext do
  let g ← getMainGoal
  let v ← elabTerm h none
  Term.synthesizeSyntheticMVarsNoPostponing
  let v ← instantiateMVars v
  if v.hasExprMVar then
    throwError "exact_by_kernel: the term {v} contains metavariables"
  g.assign v
  replaceMainGoal []

end ExactByKernel
