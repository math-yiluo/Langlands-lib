/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# The unbounded derived base change map restricts to the bounded below one

For a commutative square of schemes `g' ≫ f = f' ≫ g`, the derived base change map
`Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` on the unbounded derived categories
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`) restricts on the bounded below derived
categories to the derived base change map `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`,
modulo the identifications `Lg^* ≅ D(g^*)` of the derived pullbacks and
`R⁺f_* ⋙ ι ≅ ι ⋙ Rf_*` of the derived pushforwards
(`AlgebraicGeometry.Etale.ι_map_derivedBaseChangeMapPlus_app`). In particular the two are
isomorphisms at the same bounded below objects
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_ι_obj_iff`), so that the base change
theorems and the pasting laws available on the bounded below derived categories apply to the
unbounded derived base change map at bounded below objects.

The proof checks the characterisation `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_ext` of
the bounded below map on the restriction of the unbounded one: on a bounded below complex both
are computed by the underived base change map
(`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_fac`,
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

open _root_.DerivedCategory

/-- The image under the inclusion `D⁺ ⥤ D` of the unit of the bounded below right derived functor
is the unit of the unbounded right derived functor, through the compatibility isomorphism
`Functor.rightDerivedFunctorPlusCompatibility`. -/
@[reassoc]
lemma _root_.CategoryTheory.Functor.ι_map_rightDerivedFunctorPlusUnit_app_comp
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    [Abelian.HasKInjectiveResolutions C] (K : HomotopyCategory.Plus C) :
    Plus.ι.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (Plus.Qh.obj K) =
      F.rightDerivedFunctorUnit.app K.obj := by
  have h : F.rightDerivedFunctorPlusιUnit.app K ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app (Plus.Qh.obj K) =
      F.ιRightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  exact h

/-- The restriction of the unbounded derived base change map to the bounded below derived
categories, as a natural transformation `R⁺f_* ⋙ D⁺(g^*) ⟶ D⁺(g'^*) ⋙ R⁺f'_*`. It is the bounded
below derived base change map (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_eq`). -/
noncomputable def derivedBaseChangeMapRestrictPlus (sq : CommSq g' f' f g) :
    (f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus ⟶
      ((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus where
  app K := Plus.ι.preimage
    (D((g)^*[A]).map (((f)_*[A]).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory A g).inv.app _ ≫
      (derivedBaseChangeMap A sq).app (Plus.ι.obj K) ≫
      R((f')_*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app _) ≫
      ((f')_*[A]).rightDerivedFunctorPlusCompatibility.inv.app
        (((g')^*[A]).mapDerivedCategoryPlus.obj K))
  naturality K L φ := by
    apply Plus.ι.map_injective
    simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Functor.map_preimage]
    have h₁ := ((f)_*[A]).rightDerivedFunctorPlusCompatibility.hom.naturality φ
    have h₂ := (leftDerivedUpperStarIsoMapDerivedCategory A g).inv.naturality
      ((R((f)_*[A])).map (Plus.ι.map φ))
    have h₃ := (derivedBaseChangeMap A sq).naturality (Plus.ι.map φ)
    have h₄ := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality (Plus.ι.map φ)
    have h₅ := ((f')_*[A]).rightDerivedFunctorPlusCompatibility.inv.naturality
      ((((g')^*[A]).mapDerivedCategoryPlus).map φ)
    simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂ h₃ h₄ h₅
    change D((g)^*[A]).map (Plus.ι.map (((f)_*[A]).rightDerivedFunctorPlus.map φ)) ≫ _ = _
    rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, reassoc_of% h₂,
      reassoc_of% h₃, ← Functor.map_comp_assoc, h₄, Functor.map_comp_assoc]
    erw [h₅]
    simp only [Category.assoc]

/-- **The unbounded derived base change map restricts to the bounded below one.** -/
theorem derivedBaseChangeMapRestrictPlus_eq (sq : CommSq g' f' f g) :
    derivedBaseChangeMapRestrictPlus A sq = derivedBaseChangeMapPlus A sq := by
  refine derivedBaseChangeMapPlus_ext A sq _ fun K ↦ ?_
  apply Plus.ι.map_injective
  simp only [derivedBaseChangeMapRestrictPlus, Functor.map_comp, Functor.map_preimage]
  have hu := Functor.ι_map_rightDerivedFunctorPlusUnit_app_comp (f)_*[A] K
  have hu' := Functor.ι_map_rightDerivedFunctorPlusUnit_app_comp (f')_*[A]
    (((g')^*[A]).mapHomotopyCategoryPlus.obj K)
  have hfac : L((g)^*[A]).map ((f)_*[A].rightDerivedFunctorUnit.app K.obj) ≫
      (derivedBaseChangeMap A sq).app (Qh.obj K.obj) ≫
      R((f')_*[A]).map ((g')^*[A].leftDerivedFunctorCounit.app K.obj) =
      (g)^*[A].leftDerivedFunctorCounit.app (((f)_*[A].mapHomotopyCategory (.up ℤ)).obj K.obj) ≫
      Qh.map ((NatTrans.mapHomotopyCategory (baseChangeMap A sq) (.up ℤ)).app K.obj) ≫
      (f')_*[A].rightDerivedFunctorUnit.app (((g')^*[A].mapHomotopyCategory (.up ℤ)).obj K.obj) :=
    derivedBaseChangeMap_app_fac A sq K.obj.as
  have hL := (leftDerivedUpperStarIsoMapDerivedCategory A g).inv.naturality
    ((f)_*[A].rightDerivedFunctorUnit.app K.obj)
  have hc := NatTrans.congr_app ((g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac)
    (((f)_*[A].mapHomotopyCategory (.up ℤ)).obj K.obj)
  have hc' := NatTrans.congr_app ((g')^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac)
    K.obj
  have hF := Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app (g)^*[A]
    ((f)_*[A].mapHomotopyCategoryPlus.obj K)
  have hF' := Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app (g')^*[A] K
  have hbc := NatTrans.ι_map_mapHomotopyCategoryPlus_app (baseChangeMap A sq) K
  have hN := (f')_*[A].rightDerivedFunctorPlusCompatibility.inv.naturality
    ((g')^*[A].mapDerivedCategoryPlusFactorsh.inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map, NatTrans.comp_app, Functor.whiskerLeft_app] at *
  have hFi : Plus.ι.map ((g')^*[A].mapDerivedCategoryPlusFactorsh.inv.app K) =
      (g')^*[A].mapDerivedCategoryFactorsh.inv.app K.obj := by
    exact congrArg Iso.inv (Iso.ext (α := Plus.ι.mapIso
      ((g')^*[A].mapDerivedCategoryPlusFactorsh.app K))
      (β := (g')^*[A].mapDerivedCategoryFactorsh.app K.obj) hF')
  have hu'' : Plus.ι.map ((f')_*[A].rightDerivedFunctorPlusUnith.app
      ((g')^*[A].mapHomotopyCategoryPlus.obj K)) =
      (f')_*[A].rightDerivedFunctorUnit.app ((g')^*[A].mapHomotopyCategoryPlus.obj K).obj ≫
        (f')_*[A].rightDerivedFunctorPlusCompatibility.inv.app
          (Plus.Qh.obj ((g')^*[A].mapHomotopyCategoryPlus.obj K)) := by
    rw [← hu', Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hisoL : (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app (Qh.obj K.obj) =
      (g')^*[A].leftDerivedFunctorCounit.app K.obj ≫
        (g')^*[A].mapDerivedCategoryFactorsh.inv.app K.obj := by
    rw [← hc', Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hisoL' : (leftDerivedUpperStarIsoMapDerivedCategory A g).inv.app
      (Qh.obj (((f)_*[A].mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj)) ≫
      (g)^*[A].leftDerivedFunctorCounit.app (((f)_*[A].mapHomotopyCategory (.up ℤ)).obj K.obj) =
      (g)^*[A].mapDerivedCategoryFactorsh.hom.app
        (((f)_*[A].mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj) := by
    rw [← hc]
    exact Iso.inv_hom_id_app_assoc _ _ _
  have e₁ : Plus.ι.map (D+((g)^*[A]).map ((f)_*[A].rightDerivedFunctorPlusUnith.app K)) =
      D((g)^*[A]).map (Plus.ι.map ((f)_*[A].rightDerivedFunctorPlusUnith.app K)) := rfl
  have e₂ : Plus.ι.map (Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap A sq)).app
      K)) = Qh.map ((HomotopyCategory.Plus.ι _).map
        ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap A sq)).app K)) := rfl
  rw [e₁, ← Functor.map_comp_assoc, hu]
  change D((g)^*[A]).map ((f)_*[A].rightDerivedFunctorUnit.app K.obj) ≫
    (leftDerivedUpperStarIsoMapDerivedCategory A g).inv.app (R((f)_*[A]).obj (Qh.obj K.obj)) ≫
    (derivedBaseChangeMap A sq).app (Qh.obj K.obj) ≫
    R((f')_*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app (Qh.obj K.obj)) ≫
    _ = _
  rw [reassoc_of% hL, hisoL, Functor.map_comp, Category.assoc, reassoc_of% hfac]
  rw [reassoc_of% hisoL', hF, e₂, hbc, hu'', Category.assoc, ← hN, hFi]
  rfl

/-- The image under the inclusion `D⁺ ⥤ D` of the bounded below derived base change map at `K` is
the unbounded derived base change map at `K`, modulo the identifications `Lg^* ≅ D(g^*)` and
`R⁺f_* ⋙ ι ≅ ι ⋙ Rf_*`. -/
lemma ι_map_derivedBaseChangeMapPlus_app (sq : CommSq g' f' f g)
    (K : Plus (Sheaf X.smallEtaleTopology A)) :
    Plus.ι.map ((derivedBaseChangeMapPlus A sq).app K) =
      D((g)^*[A]).map (((f)_*[A]).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A g).inv.app _ ≫
        (derivedBaseChangeMap A sq).app (Plus.ι.obj K) ≫
        R((f')_*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app _) ≫
        ((f')_*[A]).rightDerivedFunctorPlusCompatibility.inv.app
          (((g')^*[A]).mapDerivedCategoryPlus.obj K) := by
  rw [← derivedBaseChangeMapRestrictPlus_eq]
  exact Plus.ι.map_preimage _

/-- **The unbounded derived base change map is an isomorphism at a bounded below object if and only
if the bounded below one is.** -/
lemma isIso_derivedBaseChangeMap_app_ι_obj_iff (sq : CommSq g' f' f g)
    (K : Plus (Sheaf X.smallEtaleTopology A)) :
    IsIso ((derivedBaseChangeMap A sq).app (Plus.ι.obj K)) ↔
      IsIso ((derivedBaseChangeMapPlus A sq).app K) := by
  rw [← isIso_iff_of_reflects_iso _ Plus.ι, ι_map_derivedBaseChangeMapPlus_app,
    isIso_comp_left_iff, isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff,
    isIso_comp_right_iff]

end Etale

end AlgebraicGeometry
