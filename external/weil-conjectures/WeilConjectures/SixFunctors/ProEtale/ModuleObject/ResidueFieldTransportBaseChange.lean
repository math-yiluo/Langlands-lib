/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# The derived base change map as an exchange morphism

The derived base change map `Lg^* Rf_* ⟶ Rf'_* Lg'^*` of pro-étale sheaves with coefficients in a
Grothendieck abelian category `A` (`ProEtale.derivedBaseChangeMap`) is the exchange morphism
(`CategoryTheory.Adjunction.exchangeRight`) of the isomorphism
`ProEtale.leftDerivedUpperStarSquareIso` along the derived adjunctions `Lf^* ⊣ Rf_*` and
`Lf'^* ⊣ Rf'_*` (`ProEtale.exchangeRight_leftDerivedUpperStarSquareIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived base change map is the exchange morphism of the isomorphism
`leftDerivedUpperStarSquareIso` of derived pullbacks along the derived adjunctions. -/
lemma exchangeRight_leftDerivedUpperStarSquareIso (sq : CommSq g' f' f g) :
    Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction A f)
        (derivedUpperStarLowerStarAdjunction A f') (leftDerivedUpperStarSquareIso A sq) =
      derivedBaseChangeMap A sq := by
  rw [Adjunction.exchangeRight_eq_mateEquiv]
  rfl

end AlgebraicGeometry.ProEtale
