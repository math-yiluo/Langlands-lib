/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestrictionData
import WeilConjectures.SixFunctors.PurCompactSupport.RefinementProperCounitIsIso

/-! Componentwise invertibility of the refinement restriction map. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

/--
Source: Stacks 0F7B and 0F7I, clopen restriction to the distinguished section.
The proper restriction map on each derived object is invertible because the
refinement fibre product decomposes into the clopen distinguished section and
its complement; extension by zero is exact on that section and the proper
counit restricts to the identity there.
(blueprint: lem-sf-refinement-open-restriction-is-iso-components).
-/
theorem refinementRestriction_component_isIso
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    IsIso (refinementRestriction R r hi M) := by
  rw [refinementRestriction_factorization R r hi M]
  letI : IsIso (refinementPull R r hi).hom := (refinementPull R r hi).isIso_hom
  letI : IsIso ((pull R c.i).map ((proEtaleRingDerivedAdjunction r.hom
      (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit.app
      ((openExtension R c.i).mapDerivedCategory.obj M))) :=
    refinementProperCounit_isIso R r M
  infer_instance

end WeilConjectures.PurCompactSupport
