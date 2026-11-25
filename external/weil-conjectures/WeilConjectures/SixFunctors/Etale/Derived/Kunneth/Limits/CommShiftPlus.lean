/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

/-!
# The isomorphisms between functors induced on bounded below derived categories commute with
shifts

For exact functors between abelian categories, the isomorphisms
`Functor.mapDerivedCategoryPlusNatIso e : D⁺(F) ≅ D⁺(G)` and
`Functor.mapDerivedCategoryPlusCompIso F G : D⁺(F ⋙ G) ≅ D⁺(F) ⋙ D⁺(G)` commute with the
shifts, being the restrictions of the corresponding isomorphisms on the unbounded derived
categories. Consequently so do the composition isomorphisms
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the derived pullbacks.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

instance commShift_mapDerivedCategoryPlusNatIso_hom {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryPlusNatIso e).hom ℤ := by
  have eq : whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι =
      (DerivedCategory.TStructure.t.plus.liftCompιIso
        (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)
        (fun X ↦ (F.mapDerivedCategoryPlus.obj X).2)).hom ≫
      whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryNatIso e).hom ≫
      (DerivedCategory.TStructure.t.plus.liftCompιIso
        (DerivedCategory.Plus.ι ⋙ G.mapDerivedCategory)
        (fun X ↦ (G.mapDerivedCategoryPlus.obj X).2)).inv := by
    ext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      ι_map_mapDerivedCategoryPlusNatIso_hom_app, ObjectProperty.liftCompιIso, Iso.refl_hom,
      Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι) ℤ := by
    rw [eq]; infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

instance commShift_mapDerivedCategoryPlusCompIso_hom (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    NatTrans.CommShift (mapDerivedCategoryPlusCompIso F G).hom ℤ := by
  have eq : whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι =
      (DerivedCategory.TStructure.t.plus.liftCompιIso
        (DerivedCategory.Plus.ι ⋙ (F ⋙ G).mapDerivedCategory)
        (fun X ↦ ((F ⋙ G).mapDerivedCategoryPlus.obj X).2)).hom ≫
      whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIso F G).inv ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (DerivedCategory.TStructure.t.plus.liftCompιIso
        (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)
        (fun X ↦ (F.mapDerivedCategoryPlus.obj X).2)).inv G.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft F.mapDerivedCategoryPlus (DerivedCategory.TStructure.t.plus.liftCompιIso
        (DerivedCategory.Plus.ι ⋙ G.mapDerivedCategory)
        (fun X ↦ (G.mapDerivedCategoryPlus.obj X).2)).inv ≫
      (Functor.associator _ _ _).inv := by
    ext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      ι_map_mapDerivedCategoryPlusCompIso_hom_app, ObjectProperty.liftCompιIso, Iso.refl_hom,
      Iso.refl_inv, NatTrans.id_app, Functor.associator_hom_app, Functor.associator_inv_app]
    erw [Category.id_comp, Category.comp_id, Functor.map_id, Category.comp_id,
      Category.comp_id, Category.comp_id, Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι) ℤ := by
    rw [eq]; infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

universe u' u

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

instance commShift_upperStarCompDerivedPlus_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂) :
    NatTrans.CommShift (upperStarCompDerivedPlus A h₁ h₂ h₁₂ hh₁₂).hom ℤ := by
  dsimp only [upperStarCompDerivedPlus, Iso.trans_hom]
  infer_instance

end AlgebraicGeometry.Etale
