/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestrictionData
import WeilConjectures.SixFunctors.PurCompactSupport.RefinementRestrictionComponentShift

/-! Shift compatibility of the specified refinement-restriction transformation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

/--
Source: Stacks 0F7B and 0F7I, exact open restriction and canonical derived
adjunction shifts.  The specified restriction transformation commutes with
ordinary integer cochain shifts.  The component identification determines the
transformation, so the shift square obtained from the clopen calculation is
independent of the chosen presentation.
Proof: the exact pullback compositor and derived adjunction counit commute with
shifts, and the component formula is their composite.
(blueprint: lem-sf-refinement-open-restriction-shift).
-/
theorem refinementRestriction_data_shift
    (θ : ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom) ⋙ pull R d.i ⟶
        (openExtension R c.i).mapDerivedCategory ⋙ pull R c.i)
    (hθ : ∀ M, θ.app M = refinementRestriction R r hi M) :
    θ.CommShift ℤ := by
  apply NatTrans.CommShift.of_core
  intro n
  constructor
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [hθ M, hθ ((shiftFunctor _ n).obj M)]
  exact refinementRestriction_component_shift R r hi n M

end WeilConjectures.PurCompactSupport
