/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# The compactly supported base change map commutes with the shifts

The exchange map `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`) commutes with the shifts
(`AlgebraicGeometry.Etale.commShift_rightDerivedLowerShriekBaseChangeMap`). Each of its
ingredients does:

* the derived adjunctions `D(g^*) ⊣ Rg_*` and `Lg^* ⊣ Rg_*`, hence the units of `Rg_*` and the
  derived base change map `Ex_*`, which is a mate;
* the isomorphisms between functors induced on derived categories by exact functors, such as
  the base change isomorphism of an extension by zero and the composition isomorphisms of
  derived pullbacks;
* the composition isomorphisms of derived pushforwards, hence the comparison isomorphisms
  between the derived lower shrieks of two compactifications.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section LowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The derived adjunction `D(g^*) ⊣ Rg_*` commutes with the shifts. -/
instance commShift_mapDerivedUpperStarLowerStarAdjunction :
    (mapDerivedUpperStarLowerStarAdjunction A g).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).commShift_of_leftAdjoint ℤ

/-- The unit of `Rg_*` commutes with the shifts. -/
instance commShift_rightDerivedLowerStarUnit :
    NatTrans.CommShift ((g)_*[A]).rightDerivedFunctorUnit ℤ :=
  haveI : ((upperStarLowerStarAdjunction A g).mapDerivedCategoryRightDerivedAdjunction).CommShift
      ℤ := commShift_mapDerivedUpperStarLowerStarAdjunction A g
  (upperStarLowerStarAdjunction A g).commShift_rightDerivedFunctorUnit

end LowerStar

section Compactification

variable [HasSmallSiteSheafify A] {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
  (r : c.Refinement d)

instance commShift_refinementLowerShriekBaseChangeDerivedIso_hom
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    NatTrans.CommShift (refinementLowerShriekBaseChangeDerivedIso A r hcart).hom ℤ := by
  dsimp only [refinementLowerShriekBaseChangeDerivedIso, Iso.trans_hom]
  infer_instance

/-- The comparison of the derived lower shrieks of two compactifications commutes with the
shifts. -/
instance commShift_rightDerivedLowerShriekOfCompactificationComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    NatTrans.CommShift (rightDerivedLowerShriekOfCompactificationComparison A r hcart) ℤ := by
  have := Functor.commShift_rightDerivedFunctorCompIso'_hom (r.hom)_*[A] (d.g)_*[A]
    (refinementLowerStarComp A r)
  have : NatTrans.CommShift (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have e : rightDerivedLowerShriekOfCompactificationComparison A r hcart =
      Functor.whiskerRight (Functor.rightUnitor D((d.i)_!open[A])).inv R((d.g)_*[A]) ≫
      Functor.whiskerRight (Functor.whiskerLeft D((d.i)_!open[A])
        (mapDerivedUpperStarLowerStarAdjunction A r.hom).unit) R((d.g)_*[A]) ≫
      (Functor.associator D((d.i)_!open[A]) (D((r.hom)^*[A]) ⋙ R((r.hom)_*[A]))
        R((d.g)_*[A])).hom ≫
      Functor.whiskerLeft D((d.i)_!open[A])
        (Functor.associator D((r.hom)^*[A]) R((r.hom)_*[A]) R((d.g)_*[A])).hom ≫
      (Functor.associator D((d.i)_!open[A]) D((r.hom)^*[A])
        (R((r.hom)_*[A]) ⋙ R((d.g)_*[A]))).inv ≫
      Functor.whiskerRight (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv
        (R((r.hom)_*[A]) ⋙ R((d.g)_*[A])) ≫
      Functor.whiskerLeft D((c.i)_!open[A])
        ((r.hom)_*[A].rightDerivedFunctorCompIso' (d.g)_*[A]
          (refinementLowerStarComp A r)).hom := by
    ext K
    simp [rightDerivedLowerShriekOfCompactificationComparison]
  rw [e]
  infer_instance

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [QuasiCompact f]

instance commShift_rightDerivedLowerShriekOfCompactificationIso_hom (c d : Compactification f) :
    NatTrans.CommShift (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom ℤ := by
  dsimp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv]
  have : NatTrans.CommShift (inv (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} Λ) (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d))) ℤ :=
    NatTrans.CommShift.of_isIso _ ℤ
  infer_instance

instance commShift_rightDerivedLowerShriekIso_hom [HasCompactification f] (c : Compactification f) :
    NatTrans.CommShift (rightDerivedLowerShriekIso Λ c).hom ℤ :=
  commShift_rightDerivedLowerShriekOfCompactificationIso_hom Λ c _

end Compactification

section UpperStar

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

instance commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  exact NatTrans.CommShift.of_iso_inv (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ

instance commShift_leftDerivedUpperStarComp_hom {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg₁₂ : g₁₂ = g₁ ≫ g₂) :
    NatTrans.CommShift (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg₁₂).hom ℤ := by
  have e : (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg₁₂).hom =
      (g₁₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp A g₁ g₂ g₁₂ hg₁₂)).hom ≫
        ((g₂)^*[A].mapDerivedCategoryCompIso (g₁)^*[A]).inv ≫
        Functor.whiskerRight (g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv D((g₁)^*[A]) ≫
        Functor.whiskerLeft L((g₂)^*[A]) (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv := by
    simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso]
  have : NatTrans.CommShift (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom A g₁
  have : NatTrans.CommShift (g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom A g₂
  have : NatTrans.CommShift (g₁₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom A g₁₂
  have : NatTrans.CommShift (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have : NatTrans.CommShift (g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have : NatTrans.CommShift ((g₂)^*[A].mapDerivedCategoryCompIso (g₁)^*[A]).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  rw [e]
  infer_instance

instance commShift_derivedSquareUpperStarIso_hom {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    NatTrans.CommShift (derivedSquareUpperStarIso A sq).hom ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarComp A f' g (g' ≫ f) sq.w).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  dsimp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The derived adjunction `Lg^* ⊣ Rg_*` is the adjunction `D(g^*) ⊣ Rg_*` transported along
`Lg^* ≅ D(g^*)`. -/
lemma derivedUpperStarLowerStarAdjunction_eq {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    derivedUpperStarLowerStarAdjunction A g =
      (mapDerivedUpperStarLowerStarAdjunction A g).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory A g).symm :=
  Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory A g)
    ((g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac).symm

/-- The derived adjunction `Lg^* ⊣ Rg_*` commutes with the shifts. -/
instance commShift_derivedUpperStarLowerStarAdjunction {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction A g).CommShift ℤ := by
  rw [derivedUpperStarLowerStarAdjunction_eq]
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  exact Adjunction.commShift_ofNatIsoLeft _ _

/-- The derived base change map `Ex_*` commutes with the shifts. -/
instance commShift_derivedBaseChangeMap {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) [HasSmallSiteSheafify A] :
    NatTrans.CommShift (derivedBaseChangeMap A sq) ℤ :=
  NatTrans.CommShift.mateEquiv (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom)

instance commShift_derivedOpenImmersionLowerShriekBaseChangeIso_inv [HasSmallSiteSheafify A]
    {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'') :
    NatTrans.CommShift (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).inv ℤ := by
  have : NatTrans.CommShift (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom ℤ := by
    have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g'').inv ℤ :=
      NatTrans.CommShift.of_iso_inv _ ℤ
    have : NatTrans.CommShift (Functor.mapDerivedCategoryCompIso (g')^*[A]
        (j')_!open[A]).inv ℤ := NatTrans.CommShift.of_iso_inv _ ℤ
    dsimp only [derivedOpenImmersionLowerShriekBaseChangeIso,
      mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
    infer_instance
  exact NatTrans.CommShift.of_iso_inv _ ℤ

variable [HasSmallSiteSheafify A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The compactly supported base change map along a compactification commutes with the
shifts. -/
instance commShift_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    NatTrans.CommShift (rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c) ℤ := by
  dsimp only [rightDerivedLowerShriekOfCompactificationBaseChangeMap]
  infer_instance

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The compactly supported base change map `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` commutes with
the shifts. -/
instance commShift_rightDerivedLowerShriekBaseChangeMap [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    NatTrans.CommShift (rightDerivedLowerShriekBaseChangeMap Λ sq) ℤ := by
  dsimp only [rightDerivedLowerShriekBaseChangeMap]
  infer_instance

end UpperStar

end Etale

end AlgebraicGeometry
