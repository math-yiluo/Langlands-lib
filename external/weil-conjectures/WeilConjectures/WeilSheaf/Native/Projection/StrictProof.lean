/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.BuiltinTactic

/-! # Stop model assembly at the first failed proof interface -/

public meta section

open Lean Elab Tactic

/-- Propagate nested proof errors immediately instead of checking a partially recovered term. -/
elab "projection_strict " ts:tacticSeq : tactic =>
  Term.withoutErrToSorry <| withoutRecover <| evalTactic ts
