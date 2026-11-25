/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Hausdorff

Ported from the `proetale` package (`Proetale.Mathlib.Topology.Separation.Hausdorff`).
-/

@[expose] public section

-- after `t2Space_iff_disjoint_nhds`
-- `by copilot`, this theorem exists in mathlib already.
@[stacks 08ZE]
theorem t2Space_iff_diagonal_closed {X : Type*} [TopologicalSpace X] :
    T2Space X ↔ IsClosed (Set.range (fun x : X ↦ (x, x))) := by
  rw [show Set.range (fun x : X ↦ (x, x)) = Set.diagonal X from Set.range_diag]
  exact t2_iff_isClosed_diagonal
