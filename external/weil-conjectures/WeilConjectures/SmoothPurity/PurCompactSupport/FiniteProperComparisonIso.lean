/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import WeilConjectures.SmoothPurity.PurCompactSupport.FiniteFreeRestrictionDirectImageMate

/-! # Finite proper coefficient comparison invertibility

Source: Stacks Tags 0GL5 and 0GL6.
(blueprint: lem-pur-compact-support-finite-proper-comparison-iso).

This lower statement isolates invertibility of the proper factor of the finite
coefficient comparison; the parent comparison theorem combines it with the
open factorization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

/-- The proper scalar mate is invertible for the finite coefficient change.
Source: Stacks Tags 0GL5 and 0GL6.
(blueprint: lem-pur-compact-support-finite-proper-comparison-iso).
Proof: finite freeness identifies the scalar restriction square with a finite
biproduct comparison; proper direct image preserves the resulting isomorphism,
and the adjunction mate preserves invertibility. -/
def finiteProperComparison {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g) ⋙
        pbcDerivedExtend (a.map V) ⟶
      pbcDerivedExtend (a.map U) ⋙
        proEtaleRingDerivedDirectImage g (S.ring V) (S.ring U) (S.pull g) :=
  ((mateEquiv (pbcDerivedScalarAdjunction (a.map U))
    (pbcDerivedScalarAdjunction (a.map V))).symm
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDerivedDirectImage g
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv))

end WeilConjectures.PurCompactSupport
