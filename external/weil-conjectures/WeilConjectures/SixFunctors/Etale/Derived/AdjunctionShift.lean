/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# The adjunctions `Rf_! ⊣ Rf^!` and `K ⊗ᴸ - ⊣ RHom(K, -)` commute with shifts

The functors `Rf_!`, `Rf^!` and `K ⊗ᴸ -` on the unbounded derived categories of étale sheaves
commute with the shift functors (`WeilConjectures.SixFunctors.Etale.Derived.Shift`). This file
equips the derived hom `RHom(K, -)` with its `CommShift` structure, as the right adjoint of
`K ⊗ᴸ -`, and shows that the adjunctions `Rf_! ⊣ Rf^!` and `K ⊗ᴸ - ⊣ RHom(K, -)` are
compatible with these structures (`CategoryTheory.Adjunction.CommShift`): their units and
counits commute with the shifts. For `Lg^* ⊣ Rg_*` this is
`AlgebraicGeometry.Etale.commShift_derivedUpperStarLowerStarAdjunction`.

## Main definitions and results

- `AlgebraicGeometry.Etale.commShiftDerivedHomObj`: `RHom(K, -)` commutes with shifts.
- `AlgebraicGeometry.Etale.commShift_derivedTensorHomAdjunction`,
  `AlgebraicGeometry.Etale.commShift_rightDerivedUpperShriekAdjunction`: the adjunctions
  `K ⊗ᴸ - ⊣ RHom(K, -)` and `Rf_! ⊣ Rf^!` commute with shifts.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The adjunction `Rf_! ⊣ Rf^!` commutes with shifts: the shift structure of `Rf^!` is the
one induced by the adjunction. -/
instance commShift_rightDerivedUpperShriekAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :
    (rightDerivedUpperShriekAdjunction Λ f).CommShift ℤ :=
  (rightDerivedUpperShriekAdjunction Λ f).commShift_of_leftAdjoint ℤ

/-- The adjunction `Rf_! ⊣ G` with an arbitrary right adjoint `G` of `Rf_!` commutes with shifts,
for the shift structure of `G` induced by the adjunction. -/
instance commShift_ofIsLeftAdjoint_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint] :
    (Adjunction.ofIsLeftAdjoint (R(f)_![A])).CommShift ℤ :=
  (Adjunction.ofIsLeftAdjoint (R(f)_![A])).commShift_of_leftAdjoint ℤ

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X : Scheme.{u}}

/-- The derived hom `RHom(K, -)` commutes with shifts, being right adjoint to `K ⊗ᴸ -`. -/
noncomputable instance commShiftDerivedHomObj
    (K : (DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ) :
    ((RHom(X)[A]).obj K).CommShift ℤ :=
  (derivedTensorHomAdjunction A K.unop).rightAdjointCommShift ℤ

/-- The adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` commutes with shifts. -/
instance commShift_derivedTensorHomAdjunction
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedTensorHomAdjunction A K).CommShift ℤ :=
  (derivedTensorHomAdjunction A K).commShift_of_leftAdjoint ℤ

end Etale

end AlgebraicGeometry
