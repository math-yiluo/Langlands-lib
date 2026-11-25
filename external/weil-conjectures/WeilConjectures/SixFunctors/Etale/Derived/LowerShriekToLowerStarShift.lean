/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The forget-supports map commutes with shifts

For a morphism `f` with chosen compactification `(i, g)`, the forget-supports map
`Rf_! ⟶ Ri_* ⋙ Rg_*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekToLowerStarComp`) and,
for `f` proper, the identification `Rf_! ≅ Rf_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`) commute with the
shifts. Each ingredient does: the units of the adjunctions `D(j_!) ⊣ D(j^*)` and
`D(g^*) ⊣ Rg_*`, and the composition isomorphism `Ri_* ⋙ Rg_* ≅ R(i ≫ g)_*`, the conjugate of
the composition isomorphism of the pullbacks.

## Main results

- `AlgebraicGeometry.Etale.commShift_rightDerivedLowerShriekToLowerStarComp`
- `AlgebraicGeometry.Etale.commShift_rightDerivedLowerShriekIsoRightDerivedLowerStar_hom`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived adjunction `D(j_!) ⊣ D(j^*)` along an open immersion commutes with the
shifts. -/
instance commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction' {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).CommShift ℤ :=
  inferInstanceAs
    ((openImmersionLowerShriekUpperStarAdjunction A j).mapDerivedCategoryAdjunction.CommShift ℤ)

/-- The derived comparison `D(j_!) ⟶ Rj_*` along an open immersion commutes with the shifts. -/
instance commShift_derivedOpenImmersionLowerShriekToLowerStar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    NatTrans.CommShift (derivedOpenImmersionLowerShriekToLowerStar A j) ℤ := by
  have : NatTrans.CommShift (inv (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit)
      ℤ := NatTrans.CommShift.of_isIso _ ℤ
  have : NatTrans.CommShift (Functor.associator D((j)_!open[A]) D((j)^*[A])
      R((j)_*[A])).inv ℤ := NatTrans.CommShift.of_iso_inv _ ℤ
  have : NatTrans.CommShift (D((j)_!open[A])).rightUnitor.inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have e : derivedOpenImmersionLowerShriekToLowerStar A j = (D((j)_!open[A])).rightUnitor.inv ≫
      (Functor.whiskerLeft D((j)_!open[A]) (mapDerivedUpperStarLowerStarAdjunction A j).unit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (inv (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit)
          R((j)_*[A])) ≫ (R((j)_*[A])).leftUnitor.hom := by
    ext K
    simp [derivedOpenImmersionLowerShriekToLowerStar]
  rw [e]
  infer_instance

/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*` commutes with the shifts. -/
instance commShift_rightDerivedLowerStarComp_hom {T S U : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ U) : NatTrans.CommShift (rightDerivedLowerStarComp A g₁ g₂).hom ℤ := by
  dsimp only [rightDerivedLowerStarComp, Iso.symm_hom]
  rw [conjugateIsoEquiv_apply_inv, Iso.symm_inv, Iso.trans_hom]
  infer_instance

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The forget-supports map `Rf_! ⟶ Ri_* ⋙ Rg_*` commutes with the shifts. -/
instance commShift_rightDerivedLowerShriekToLowerStarComp :
    NatTrans.CommShift (rightDerivedLowerShriekToLowerStarComp A f) ℤ :=
  inferInstanceAs (NatTrans.CommShift (Functor.whiskerRight
    (derivedOpenImmersionLowerShriekToLowerStar A _) _) ℤ)

/-- For a proper morphism `f`, the identification `Rf_! ≅ Rf_*` commutes with the shifts. -/
instance commShift_rightDerivedLowerShriekIsoRightDerivedLowerStar_hom [IsProper f] :
    NatTrans.CommShift (rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom ℤ := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom]
  have h : ∀ {g₁ g₂ : X ⟶ Y} (h : g₁ = g₂),
      NatTrans.CommShift (rightDerivedLowerStarCongr A h).hom ℤ := by
    rintro _ _ rfl
    rw [rightDerivedLowerStarCongr_refl]
    exact inferInstanceAs (NatTrans.CommShift (𝟙 _) ℤ)
  have := h (HasCompactification.compactification f).comm.symm
  infer_instance

/-- For a proper morphism `f`, the inverse of the identification `Rf_! ≅ Rf_*` commutes with
the shifts. -/
instance commShift_rightDerivedLowerShriekIsoRightDerivedLowerStar_inv [IsProper f] :
    NatTrans.CommShift (rightDerivedLowerShriekIsoRightDerivedLowerStar A f).inv ℤ :=
  NatTrans.CommShift.of_iso_inv _ ℤ

end Etale

end AlgebraicGeometry
