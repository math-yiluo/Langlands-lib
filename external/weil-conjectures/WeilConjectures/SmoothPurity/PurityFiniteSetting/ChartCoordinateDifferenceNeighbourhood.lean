/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential

/-! # Centred etale coordinate-difference neighbourhoods

Source: chart proof, Step 1.
(blueprint: lem-pur-chart-coordinate-difference-neighbourhood).

This extracts the existing proved geometry with its declaration names and data unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The actual coordinate differences y_i-x_i, based at the first projection.
Source: chart proof, Steps 1--2
(blueprint: lem-pur-chart-coordinate-difference-neighbourhood). -/
def chartCoordinateDifferences {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) :
    pullback h h ⟶ AffineSpace (ULift.{u} (Fin d)) U :=
  AffineSpace.homOfVector (pullback.fst h h) fun i ↦
    (pullback.snd h h ≫ u).appTop (AffineSpace.coord V i) -
      (pullback.fst h h ≫ u).appTop (AffineSpace.coord V i)

end WeilConjectures.PurityFiniteSetting
