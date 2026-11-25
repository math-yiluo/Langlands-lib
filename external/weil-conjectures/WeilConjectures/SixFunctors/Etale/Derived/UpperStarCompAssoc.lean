/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
public import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Associativity of the composition isomorphisms of the bounded below derived pullbacks

The composition isomorphisms `AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the pullbacks
on the bounded below derived categories of étale sheaves are associative: this is the
associativity of the composition isomorphisms `AlgebraicGeometry.Etale.upperStarComp` of the
underived pullbacks (`AlgebraicGeometry.Etale.upperStarComp_assoc'`), transported along the
factorization of `D⁺(f^*)` through the homotopy category. Together with the unit laws of
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity`, the bounded below derived
pullbacks form a pseudofunctor.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

omit [HasSmallSiteSheafify A] in
/-- **Associativity of the composition isomorphisms of the bounded below derived pullbacks.** -/
lemma Etale.upperStarCompDerivedPlus_assoc {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h)
    (hfgh : fgh = fg ≫ h) :
    (upperStarCompDerivedPlus A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (upperStarCompDerivedPlus A g h gh hgh).hom
          ((f)^*[A]).mapDerivedCategoryPlus =
      (upperStarCompDerivedPlus A fg h fgh hfgh).hom ≫
        Functor.whiskerLeft ((h)^*[A]).mapDerivedCategoryPlus
          (upperStarCompDerivedPlus A f g fg hfg).hom := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso _) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (((f)^*[A]).mapDerivedCategoryPlus.map (((g)^*[A]).mapDerivedCategoryPlus.map
      (((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
    ((f)^*[A]).mapDerivedCategoryPlus.map (((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
      (((h)^*[A]).mapHomotopyCategoryPlus.obj K)) ≫
    ((f)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
      (((g)^*[A]).mapHomotopyCategoryPlus.obj (((h)^*[A]).mapHomotopyCategoryPlus.obj K)))]
  -- the left hand side
  have hL₁ := upperStarCompDerivedPlus_hom_app_factorsh A g h gh hgh K
  have hL₂ := upperStarCompDerivedPlus_hom_app_factorsh A f gh fgh
    (by rw [hfgh, hfg, hgh, Category.assoc]) K
  have hn₁ := ((f)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarComp A g h gh hgh).hom).app K)
  -- the right hand side
  have hR₁ := upperStarCompDerivedPlus_hom_app_factorsh A f g fg hfg
    (((h)^*[A]).mapHomotopyCategoryPlus.obj K)
  have hR₂ := upperStarCompDerivedPlus_hom_app_factorsh A fg h fgh hfgh K
  have hn₂ := (upperStarCompDerivedPlus A f g fg hfg).hom.naturality
    (((h)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn₁ hn₂
  have key := congrArg (fun φ ↦ DerivedCategory.Plus.Qh.map
    ((NatTrans.mapHomotopyCategoryPlus φ).app K))
    (Etale.upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh)
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app, Functor.map_comp,
    NatTrans.mapHomotopyCategoryPlus_whiskerRight_app,
    NatTrans.mapHomotopyCategoryPlus_whiskerLeft_app] at key
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc ((upperStarCompDerivedPlus A g h gh hgh).hom.app _), hL₁, Functor.map_comp,
    Category.assoc]
  erw [hn₁]
  rw [reassoc_of% hL₂]
  -- the right hand side
  rw [← reassoc_of% hn₂]
  slice_rhs 3 5 => rw [hR₁]
  slice_rhs 1 3 => rw [hR₂]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) key

end AlgebraicGeometry
