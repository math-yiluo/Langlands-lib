/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.ExtremallyDisconnected

/-!
# The Stone–Čech compactification of a discrete space is extremally disconnected

`StoneCech.projective` says that `StoneCech X` is projective among compact Hausdorff spaces for
a discrete `X`, and projective compact Hausdorff spaces are extremally disconnected. We record
the resulting instance; it makes `StoneCech X` (and its finite products) profinite.
-/

@[expose] public section

instance StoneCech.extremallyDisconnected {X : Type*} [TopologicalSpace X] [DiscreteTopology X] :
    ExtremallyDisconnected (StoneCech X) :=
  StoneCech.projective.extremallyDisconnected
