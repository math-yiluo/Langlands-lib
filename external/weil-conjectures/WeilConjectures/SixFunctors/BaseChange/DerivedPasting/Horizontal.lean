/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical

/-!
# Horizontal pasting law for the derived base change map

For two squares pasted horizontally, the derived base change map
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` of the pasted square is the composite of the
derived base change maps of the two squares, modulo the composition isomorphisms
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the derived pullbacks
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_horiz`).

The pasting laws are collected in `WeilConjectures.SixFunctors.BaseChange.DerivedPasting`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

section Horizontal

variable {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''}
  {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}

/-- The underived horizontal pasting law, without associators. -/
lemma Etale.baseChangeMap_paste_horiz' (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    Etale.baseChangeMap A sq =
      Functor.whiskerLeft ((f)_*[A]) (Etale.upperStarComp A h g).hom ≫
        Functor.whiskerRight (Etale.baseChangeMap A sq₁) ((h)^*[A]) ≫
        Functor.whiskerLeft ((g')^*[A]) (Etale.baseChangeMap A sq₂) ≫
        Functor.whiskerRight (Etale.upperStarComp A g'' g').inv ((f'')_*[A]) := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [Etale.baseChangeMap_paste_horiz_app A sq₁ sq₂ sq]
  rfl

/-- **Horizontal pasting of the derived base change maps**: for two squares pasted
horizontally, the derived base change map of the pasted square is the composite
`(h ≫ g)^* Rf_* ≅ h^* g^* Rf_* ⟶ h^* Rf'_* g'^* ⟶ Rf''_* g''^* g'^* ≅ Rf''_* (g'' ≫ g')^*` of
the derived base change maps of the two squares, modulo the composition isomorphisms
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the derived pullbacks along the
horizontal maps.
(blueprint: `lemma-identity-pasting`,
`lemma-identity-pasting`) -/
lemma Etale.derivedBaseChangeMapPlus_paste_horiz (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    Etale.derivedBaseChangeMapPlus A sq =
      Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
          (Etale.upperStarCompDerivedPlus A h g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A sq₁)
          ((h)^*[A]).mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((g')^*[A]).mapDerivedCategoryPlus
          (Etale.derivedBaseChangeMapPlus A sq₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.upperStarCompDerivedPlus A g'' g').inv
          (f'')_*[A].rightDerivedFunctorPlus := by
  -- it suffices to prove the equation after composing with the composition isomorphism
  suffices hmain : Etale.derivedBaseChangeMapPlus A sq ≫
      Functor.whiskerRight (Etale.upperStarCompDerivedPlus A g'' g').hom
        (f'')_*[A].rightDerivedFunctorPlus =
      Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
          (Etale.upperStarCompDerivedPlus A h g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A sq₁)
          ((h)^*[A]).mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((g')^*[A]).mapDerivedCategoryPlus
          (Etale.derivedBaseChangeMapPlus A sq₂) ≫
        (Functor.associator _ _ _).inv by
    rw [← cancel_mono (Functor.whiskerRight (Etale.upperStarCompDerivedPlus A g'' g').hom
      (f'')_*[A].rightDerivedFunctorPlus), hmain]
    simp only [Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
      Functor.whiskerRight_id', Category.comp_id]
  refine Functor.rightDerived_ext _ (Etale.rightDerivedLowerStarPlusCompUpperStarUnit A f (h ≫ g))
    (HomotopyCategory.Plus.quasiIso _) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, id_comp,
    Etale.rightDerivedLowerStarPlusCompUpperStarUnit, comp_id]
  -- the left hand side: the characterisation of the derived base change map of `sq`
  rw [Etale.derivedBaseChangeMapPlus_fac_app_assoc A sq K]
  have hfac₁ := Etale.derivedBaseChangeMapPlus_fac_app A sq₁ K
  have hfac₂ := Etale.derivedBaseChangeMapPlus_fac_app A sq₂
    (((g')^*[A]).mapHomotopyCategoryPlus.obj K)
  -- naturality of the composition isomorphism along the unit of `Rf_*`
  have hnatC := (Etale.upperStarCompDerivedPlus A h g).hom.naturality
    ((f)_*[A].rightDerivedFunctorPlusUnith.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatC
  -- naturality of the derived base change map of the right square along `factorsh`
  have hnat₂ : ((h)^*[A]).mapDerivedCategoryPlus.map ((f')_*[A].rightDerivedFunctorPlus.map
        (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K)) ≫
      (Etale.derivedBaseChangeMapPlus A sq₂).app
        (((g')^*[A]).mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (Etale.derivedBaseChangeMapPlus A sq₂).app
        (DerivedCategory.Plus.Qh.obj (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) ≫
      (f'')_*[A].rightDerivedFunctorPlus.map (((g'')^*[A]).mapDerivedCategoryPlus.map
        (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K)) :=
    (Etale.derivedBaseChangeMapPlus A sq₂).naturality
      (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K)
  -- naturality of `factorsh` for `h^*` along the underived base change map of the left square
  have hnatF : ((h)^*[A]).mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)) ≫
      ((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        ((f')_*[A].mapHomotopyCategoryPlus.obj (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) =
      ((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((g)^*[A]).mapHomotopyCategoryPlus.obj ((f)_*[A].mapHomotopyCategoryPlus.obj K)) ≫
      DerivedCategory.Plus.Qh.map (((h)^*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)) :=
    ((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K)
  have hC₁ := Etale.upperStarCompDerivedPlus_hom_app_factorsh A h g (h ≫ g) rfl
    ((f)_*[A].mapHomotopyCategoryPlus.obj K)
  have hC₂ := Etale.upperStarCompDerivedPlus_hom_app_factorsh A g'' g' (g'' ≫ g') rfl K
  -- the composition isomorphism on the right, rearranged
  have hC₂' : ((g'' ≫ g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K ≫
      (Etale.upperStarCompDerivedPlus A g'' g').hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A g'' g').hom).app K) ≫
        ((g'')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app
          (((g')^*[A]).mapHomotopyCategoryPlus.obj K) ≫
        ((g'')^*[A]).mapDerivedCategoryPlus.map
          (((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app K) := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, ← Category.assoc, ← Category.assoc, ← hC₂]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hpaste : (NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app K =
      (NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A h g).hom).app
          ((f)_*[A].mapHomotopyCategoryPlus.obj K) ≫
        ((h)^*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₁)).app K) ≫
        (NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq₂)).app
          (((g')^*[A]).mapHomotopyCategoryPlus.obj K) ≫
        ((f'')_*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').inv).app K) := by
    rw [Etale.baseChangeMap_paste_horiz' A sq₁ sq₂ sq, NatTrans.mapHomotopyCategoryPlus_comp,
      NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.mapHomotopyCategoryPlus_comp,
      NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    rfl
  have hη : DerivedCategory.Plus.Qh.map (((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K)) ≫
      (f'')_*[A].rightDerivedFunctorPlusUnith.app
        (((g'')^*[A]).mapHomotopyCategoryPlus.obj (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) =
      (f'')_*[A].rightDerivedFunctorPlusUnith.app
        (((g'' ≫ g')^*[A]).mapHomotopyCategoryPlus.obj K) ≫
      (f'')_*[A].rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K)) :=
    (f'')_*[A].rightDerivedFunctorPlusUnith.naturality
      ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K)
  have hcancel : ((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').inv).app K) ≫
      ((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K) = 𝟙 _ := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp,
      Iso.inv_hom_id, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
  -- `rw` is avoided below where its unifier would unfold the derived functors: `simp only`
  -- works up to reducible transparency and is fast here.
  -- the right hand side: expand the left square and push the base change map of the right
  -- square through `factorsh`
  rw [reassoc_of% hnatC, ← Functor.map_comp_assoc, hfac₁, Functor.map_comp, Functor.map_comp,
    Functor.map_comp]
  simp only [Category.assoc]
  simp only [hnat₂, reassoc_of% hfac₂, reassoc_of% hnatF, reassoc_of% hC₁]
  -- the left hand side: rearrange the composition isomorphism and use the underived pasting
  have hc2 : DerivedCategory.Plus.Qh.map (((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').inv).app K)) ≫
      DerivedCategory.Plus.Qh.map (((f'')_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g'' g').hom).app K)) = 𝟙 _ := by
    rw [← DerivedCategory.Plus.Qh.map_comp, hcancel, DerivedCategory.Plus.Qh.map_id]
  simp only [← Functor.map_comp]
  simp only [hC₂']
  simp only [Functor.map_comp]
  simp only [← reassoc_of% hη, hpaste, Functor.map_comp, Category.assoc, reassoc_of% hc2]

end Horizontal

end AlgebraicGeometry
