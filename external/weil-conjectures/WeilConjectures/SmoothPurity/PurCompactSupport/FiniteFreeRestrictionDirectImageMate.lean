/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeRestrictionDirectImageMate

/-! # The finite-free scalar mate of restriction and direct image

Source: Stacks Project, Tags 0B56 and 07A6.
(blueprint: lem-pur-finite-free-restriction-direct-image-mate).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

/-- The inverse scalar mate of the canonical restriction/direct-image square is invertible
for a globally finite-free coefficient extension.

Source: Stacks Project, Tags 0B56 (projection formula) and 07A6 (derived adjunction).
(blueprint: lem-pur-finite-free-restriction-direct-image-mate).

This is `FiniteFreeDirectImage.restrictionDirectImageMate_isIso` for the coefficient
sheaves and coefficient change of `a`. The conclusion is the explicit mate expression;
it does not import the higher compact-support comparison module. -/
theorem finiteFreeRestrictionDirectImageMate_isIso {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) (d : ℕ)
    (hfree : Nonempty
      ((pbcRestrict (a.map V)).obj
          (SheafOfModules.unit ((adicLisseForget V).obj (S.ring V))) ≅
        ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget V).obj (R.ring V)))) :
    IsIso (((mateEquiv (pbcDerivedScalarAdjunction (a.map U))
      (pbcDerivedScalarAdjunction (a.map V))).symm
        (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedDirectImage g
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv))) :=
  FiniteFreeDirectImage.restrictionDirectImageMate_isIso g _ _ _ _ _ _ _ _ _ d hfree

end WeilConjectures.PurCompactSupport
