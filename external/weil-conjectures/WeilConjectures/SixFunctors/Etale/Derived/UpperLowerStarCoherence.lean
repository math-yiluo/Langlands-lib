/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!

# Derived Upper Star and Lower Star

# Main Results

- `AlgebraicGeometry.Etale.rightDerivedLowerStar` : total right derived of lower star, the
  generic `Functor.rightDerivedFunctor` applied to the underived pushforward `(g)_*[A]`,
  written `R((g)_*[A])`.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` : total right derived of lower star on
  the bounded below derived category, written `R+((g)_*[A])`.

- `AlgebraicGeometry.Etale.upperStarIdDerivedPlus` and
  `AlgebraicGeometry.Etale.upperStarCompDerivedPlus`: the identity isomorphism
  `D(𝟙 V)^*⁺ ≅ 𝟭` and the composition isomorphism `D(h₁ ≫ h₂)^*⁺ ≅ D(h₂)^*⁺ ⋙ D(h₁)^*⁺` of
  the pullbacks on the bounded below derived categories.

- `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus`: the identity isomorphism
  `R(𝟙 V)_*⁺ ≅ 𝟭` of the pushforward on the bounded below derived categories. The
  corresponding composition isomorphism is `Functor.rightDerivedFunctorPlusCompIso'`
  applied to `AlgebraicGeometry.Etale.lowerStarComp`.

- `AlgebraicGeometry.Etale.derivedPlus_unit_comp_upperStarIdDerivedPlus` and
  `AlgebraicGeometry.Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus`: the units of
  the bounded below derived adjunctions `D(g)^*⁺ ⊣ R(g)_*⁺` are compatible with these
  identity and composition isomorphisms.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section DerivedLowerStar

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctor

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on the
*bounded below* derived categories of étale sheaves.

Blueprint `def-weil-pbc-direct-image`: Direct image and its derived functor

The direct image `g_*` is `AlgebraicGeometry.Etale.lowerStar`, with
`(g_* F)(W) = F(W ×_Y Z)` (`AlgebraicGeometry.Etale.lowerStar_obj_val_obj`); this is its right
derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)`, computed by injective resolutions, and
`R^q g_* F` is the `q`-th cohomology sheaf of `Rg_* F`. -/
noncomputable def rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctorPlus

end Etale

end DerivedLowerStar

section IdentityAndComposition

namespace Etale

variable {Y : Scheme.{u}}

variable (V : Scheme.{u})

/-- The identity isomorphism `D(𝟙 V)^*⁺ ≅ 𝟭` of the pullback along the identity on the
bounded below derived categories, induced by `AlgebraicGeometry.Etale.upperStarId`. -/
noncomputable def upperStarIdDerivedPlus :
    ((𝟙 V)^*[A]).mapDerivedCategoryPlus ≅
      𝟭 (DerivedCategory.Plus (Sheaf V.smallEtaleTopology A)) :=
  Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarId A V) ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- On the image of a bounded below complex, `AlgebraicGeometry.Etale.upperStarIdDerivedPlus`
is the factorization `Functor.mapDerivedCategoryPlusFactorsh` followed by the levelwise
image of `AlgebraicGeometry.Etale.upperStarId`. -/
lemma upperStarIdDerivedPlus_hom_app
    (K : HomotopyCategory.Plus (Sheaf V.smallEtaleTopology A)) :
    (upperStarIdDerivedPlus A V).hom.app (DerivedCategory.Plus.Qh.obj K) =
      ((𝟙 V)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K) := by
  rw [upperStarIdDerivedPlus, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]

/-- The identity isomorphism `R(𝟙 V)_*⁺ ≅ 𝟭` of the pushforward along the identity on the
bounded below derived categories, induced by `AlgebraicGeometry.Etale.lowerStarId`. -/
noncomputable def lowerStarIdDerivedPlus :
    ((𝟙 V)_*[A]).rightDerivedFunctorPlus ≅
      𝟭 (DerivedCategory.Plus (Sheaf V.smallEtaleTopology A)) :=
  Functor.rightDerivedFunctorPlusNatIso (Etale.lowerStarId A V) ≪≫
    Functor.rightDerivedFunctorPlusIdIso _

omit [HasSmallSiteSheafify A] in
/-- The characterization of `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus`: composing the
unit of the right derived functor with it gives the levelwise image of
`AlgebraicGeometry.Etale.lowerStarId`. -/
lemma lowerStarIdDerivedPlus_hom_app_fac
    (K : HomotopyCategory.Plus (Sheaf V.smallEtaleTopology A)) :
    ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnith.app K ≫
        (lowerStarIdDerivedPlus A V).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).hom).app K) := by
  have hn : (Functor.rightDerivedFunctorPlusNatIso (Etale.lowerStarId A V)).hom =
      Functor.rightDerivedFunctorPlusNatTrans (Etale.lowerStarId A V).hom := rfl
  rw [lowerStarIdDerivedPlus, Iso.trans_hom, NatTrans.comp_app, hn, ← Category.assoc,
    Functor.rightDerivedFunctorPlusNatTrans_app, Category.assoc,
    Functor.rightDerivedFunctorPlusIdIso_fac_app,
    Functor.mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
  have hid : DerivedCategory.Plus.Qh.map (𝟙 K) = 𝟙 (DerivedCategory.Plus.Qh.obj K) :=
    DerivedCategory.Plus.Qh.map_id K
  rw [hid]
  exact Category.comp_id _

omit [HasSmallSiteSheafify A] in
/-- The inverse form of `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus_hom_app_fac`: on the
image of a bounded below complex, the inverse of
`AlgebraicGeometry.Etale.lowerStarIdDerivedPlus` is the levelwise image of the inverse of
`AlgebraicGeometry.Etale.lowerStarId` followed by the unit of the right derived functor. -/
lemma lowerStarIdDerivedPlus_inv_app
    (K : HomotopyCategory.Plus (Sheaf V.smallEtaleTopology A)) :
    (lowerStarIdDerivedPlus A V).inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K) ≫
        ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnith.app K := by
  rw [← cancel_mono ((lowerStarIdDerivedPlus A V).hom.app (DerivedCategory.Plus.Qh.obj K)),
    Iso.inv_hom_id_app, Category.assoc, lowerStarIdDerivedPlus_hom_app_fac,
    ← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
    NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app]
  exact (DerivedCategory.Plus.Qh.map_id _).symm

/-- **The derived unit for the identity morphism**: the unit of the bounded below derived
adjunction `D(𝟙 V)^*⁺ ⊣ R(𝟙 V)_*⁺` is, modulo the identity isomorphism
`AlgebraicGeometry.Etale.upperStarIdDerivedPlus` of the pullback, the inverse of the
identity isomorphism `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus` of the pushforward. -/
lemma derivedPlus_unit_comp_upperStarIdDerivedPlus :
    (Etale.upperStarLowerStarAdjunction A (𝟙 V)).derivedPlus.unit ≫
        Functor.whiskerRight (upperStarIdDerivedPlus A V).hom
          (((𝟙 V)_*[A]).rightDerivedFunctorPlus) =
      (lowerStarIdDerivedPlus A V).inv := by
  rw [← cancel_epi (lowerStarIdDerivedPlus A V).hom, Iso.hom_inv_id]
  refine Functor.rightDerived_ext (((𝟙 V)_*[A]).rightDerivedFunctorPlus)
    (((𝟙 V)_*[A]).rightDerivedFunctorPlusUnith) (HomotopyCategory.Plus.quasiIso _) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app]
  have hnat : DerivedCategory.Plus.Qh.map (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K)) ≫
      ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnith.app
        ((𝟭 (Sheaf V.smallEtaleTopology A)).mapHomotopyCategoryPlus.obj K) =
      ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnith.app
          (((𝟙 V)^*[A]).mapHomotopyCategoryPlus.obj K) ≫
        ((𝟙 V)_*[A]).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K)) :=
    ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnith.naturality _
  have hcomb : (NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).hom).app K ≫
      (Etale.upperStarLowerStarAdjunction A (𝟙 V)).mapHomotopyCategoryPlus.unit.app K ≫
        ((𝟙 V)_*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K) =
      𝟙 (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.obj K) := by
    rw [Adjunction.mapHomotopyCategoryPlus_unit_app_comp_id
        (Etale.upperStarLowerStarAdjunction A (𝟙 V)) (Etale.upperStarId A V)
        (Etale.lowerStarId A V) (Etale.upperStarId_hom_app_unit_app A V) K,
      ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.hom_inv_id]
    exact NatTrans.congr_app (NatTrans.mapHomotopyCategoryPlus_id ((𝟙 V)_*[A])) K
  have hQ : DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).hom).app K) ≫
      DerivedCategory.Plus.Qh.map
        ((Etale.upperStarLowerStarAdjunction A (𝟙 V)).mapHomotopyCategoryPlus.unit.app K) ≫
        DerivedCategory.Plus.Qh.map (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K)) =
      𝟙 (DerivedCategory.Plus.Qh.obj (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.obj K)) := by
    rw [← DerivedCategory.Plus.Qh.map_comp, ← DerivedCategory.Plus.Qh.map_comp]
    exact (congrArg DerivedCategory.Plus.Qh.map hcomb).trans
      (DerivedCategory.Plus.Qh.map_id _)
  rw [← Category.assoc, lowerStarIdDerivedPlus_hom_app_fac, upperStarIdDerivedPlus_hom_app,
    Functor.map_comp, Adjunction.derivedPlus_unit_app_fac_assoc, ← hnat, reassoc_of% hQ]
  exact (Category.comp_id (((𝟙 V)_*[A]).rightDerivedFunctorPlusUnith.app K)).symm

variable {V}

omit [HasSmallSiteSheafify A] in
/-- The composition isomorphism `Functor.rightDerivedFunctorPlusCompIso'` cancels the
identity isomorphism `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus`, provided the
underlying isomorphism `e` of pushforwards cancels
`AlgebraicGeometry.Etale.lowerStarId`. -/
lemma lowerStarIdDerivedPlus_inv_comp_rightDerivedFunctorPlusCompIso' (g : V ⟶ Y)
    [(((𝟙 V)_*[A])).PreservesInjectiveObjects]
    (e : ((𝟙 V)_*[A]) ⋙ ((g)_*[A]) ≅ (g)_*[A])
    (he : Functor.whiskerRight (Etale.lowerStarId A V).inv ((g)_*[A]) ≫ e.hom =
      𝟙 ((g)_*[A])) :
    Functor.whiskerRight (lowerStarIdDerivedPlus A V).inv
          (((g)_*[A]).rightDerivedFunctorPlus) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((𝟙 V)_*[A]) ((g)_*[A]) e).hom =
      𝟙 (((g)_*[A]).rightDerivedFunctorPlus) := by
  refine Functor.rightDerived_ext (((g)_*[A]).rightDerivedFunctorPlus)
    (((g)_*[A]).rightDerivedFunctorPlusUnith) (HomotopyCategory.Plus.quasiIso _) _ _ _ ?_
  ext K : 2
  have hnat : DerivedCategory.Plus.Qh.map (((g)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K)) ≫
      ((g)_*[A]).rightDerivedFunctorPlusUnith.app
        (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.obj K) =
      ((g)_*[A]).rightDerivedFunctorPlusUnith.app K ≫
        ((g)_*[A]).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K)) :=
    ((g)_*[A]).rightDerivedFunctorPlusUnith.naturality _
  have hfac := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac
    ((𝟙 V)_*[A]) ((g)_*[A]) e) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hfac ⊢
  have hfac2 := (Functor.rightDerivedFunctorPlusCompUnit_app_assoc ((𝟙 V)_*[A]) ((g)_*[A]) K
    ((Functor.rightDerivedFunctorPlusCompIso' ((𝟙 V)_*[A]) ((g)_*[A]) e).hom.app
      (DerivedCategory.Plus.Qh.obj K))).symm.trans hfac
  have hm : ((g)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K) =
      (NatTrans.mapHomotopyCategoryPlus
        (Functor.whiskerRight (Etale.lowerStarId A V).inv ((g)_*[A]))).app K := rfl
  have hcomp : ((g)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K) ≫
      (NatTrans.mapHomotopyCategoryPlus e.hom).app K =
      𝟙 (((g)_*[A]).mapHomotopyCategoryPlus.obj K) := by
    rw [hm, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, he]
    exact NatTrans.congr_app (NatTrans.mapHomotopyCategoryPlus_id ((g)_*[A])) K
  have hQ : DerivedCategory.Plus.Qh.map (((g)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K)) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) =
      𝟙 (DerivedCategory.Plus.Qh.obj (((g)_*[A]).mapHomotopyCategoryPlus.obj K)) :=
    (DerivedCategory.Plus.Qh.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Plus.Qh.map hcomp).trans
        (DerivedCategory.Plus.Qh.map_id _))
  rw [lowerStarIdDerivedPlus_inv_app, Functor.map_comp, Category.assoc,
    ← reassoc_of% hnat, hfac2, reassoc_of% hQ]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `D(h₁ ≫ h₂)^*⁺ ≅ D(h₂)^*⁺ ⋙ D(h₁)^*⁺` of the pullbacks on
the bounded below derived categories, induced by `AlgebraicGeometry.Etale.upperStarComp`. -/
noncomputable def upperStarCompDerivedPlus (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) :
    ((h₁₂)^*[A]).mapDerivedCategoryPlus ≅
      ((h₂)^*[A]).mapDerivedCategoryPlus ⋙ ((h₁)^*[A]).mapDerivedCategoryPlus :=
  Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

omit [HasSmallSiteSheafify A] in
@[reassoc]
lemma upperStarCompDerivedPlus_hom_app_factorsh (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch)
    (K : HomotopyCategory.Plus (Sheaf R.smallEtaleTopology A)) :
    (Etale.upperStarCompDerivedPlus A h₁ h₂ h₁₂ hh₁₂).hom.app
          (DerivedCategory.Plus.Qh.obj K) ≫
        ((h₁)^*[A]).mapDerivedCategoryPlus.map
          (((h₂)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        ((h₁)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((h₂)^*[A]).mapHomotopyCategoryPlus.obj K) =
      ((h₁₂)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom).app K) := by
  simp only [Etale.upperStarCompDerivedPlus, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh]
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]

/-- **The derived unit for a composite morphism**: the unit of the bounded below derived
adjunction `D(h₁ ≫ h₂)^*⁺ ⊣ R(h₁ ≫ h₂)_*⁺` is, modulo the composition isomorphism
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the pullbacks, the composite of the
units of `D(h₂)^*⁺ ⊣ R(h₂)_*⁺` and `D(h₁)^*⁺ ⊣ R(h₁)_*⁺`, followed by the composition
isomorphism of the derived pushforwards. -/
lemma derivedPlus_unit_comp_upperStarCompDerivedPlus (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch)
    (Z : DerivedCategory.Plus (Sheaf R.smallEtaleTopology A)) :
    haveI : (((h₁)_*[A])).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (Etale.upperStarLowerStarAdjunction A h₁)
    (Etale.upperStarLowerStarAdjunction A h₁₂).derivedPlus.unit.app Z ≫
        ((h₁₂)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.upperStarCompDerivedPlus A h₁ h₂ h₁₂ hh₁₂).hom.app Z) =
      (Etale.upperStarLowerStarAdjunction A h₂).derivedPlus.unit.app Z ≫
        ((h₂)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.upperStarLowerStarAdjunction A h₁).derivedPlus.unit.app
            (((h₂)^*[A]).mapDerivedCategoryPlus.obj Z)) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((h₁)_*[A]) ((h₂)_*[A])
            (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂)).hom.app
          (((h₁)^*[A]).mapDerivedCategoryPlus.obj
            (((h₂)^*[A]).mapDerivedCategoryPlus.obj Z)) := by
  have : (((h₁)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A h₁)
  have hXi : (Functor.rightDerivedFunctorPlusCompIso' ((h₁)_*[A]) ((h₂)_*[A])
        (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂)).hom =
      (Functor.rightDerivedFunctorPlusCompIso ((h₁)_*[A]) ((h₂)_*[A])).inv ≫
        Functor.rightDerivedFunctorPlusNatTrans
          (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).hom := rfl
  have hC := Adjunction.derivedPlus_unit_comp_app
    (Etale.upperStarLowerStarAdjunction A h₁₂)
    ((Etale.upperStarLowerStarAdjunction A h₂).comp
      (Etale.upperStarLowerStarAdjunction A h₁))
    (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂) (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂)
    (Etale.upperStarComp_hom_app_unit_app A h₁ h₂ · h₁₂ hh₁₂) Z
  have hcompunit := Adjunction.derivedPlus_comp_unit_app
    (Etale.upperStarLowerStarAdjunction A h₂) (Etale.upperStarLowerStarAdjunction A h₁) Z
  have hnatCI := (Functor.rightDerivedFunctorPlusCompIso ((h₁)_*[A]) ((h₂)_*[A])).inv.naturality
    ((Functor.mapDerivedCategoryPlusCompIso ((h₂)^*[A]) ((h₁)^*[A])).hom.app Z)
  have hnatN := (Functor.rightDerivedFunctorPlusNatTrans
      (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).hom).naturality
    ((Functor.mapDerivedCategoryPlusCompIso ((h₂)^*[A]) ((h₁)^*[A])).hom.app Z)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatCI hnatN
  have hPhi : (Etale.upperStarCompDerivedPlus A h₁ h₂ h₁₂ hh₁₂).hom.app Z =
      (Functor.mapDerivedCategoryPlusNatIso
          (Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂)).hom.app Z ≫
        (Functor.mapDerivedCategoryPlusCompIso ((h₂)^*[A]) ((h₁)^*[A])).hom.app Z := rfl
  rw [hPhi, Functor.map_comp, ← Category.assoc, hC, Category.assoc, ← hnatN,
    ← reassoc_of% hcompunit, hXi]
  simp only [NatTrans.comp_app]
  rw [reassoc_of% hnatCI, Iso.hom_inv_id_app_assoc]

end Etale

end IdentityAndComposition

end AlgebraicGeometry
