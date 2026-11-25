/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySingleFlatNaturality

/-! # Normalization of the degree-zero comparison for exact functors -/

@[expose] public section

universe uC uD vC vD wC wD

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The comparison obtained from the left-derived counit agrees with the ordinary
exact-functor comparison. -/
lemma puritySingleComparison_app_eq_exact (P : C) :
    F.puritySingleComparison.app P =
      F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.singleFunctor C 0).obj P) ≫
        (F.mapDerivedCategorySingleFunctor 0).hom.app P := by
  simp only [puritySingleComparison, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← leftDerivedFunctorIsoMapDerivedCategory_hom_app_comp_factorsh]
  simp only [Category.assoc, Functor.comp_obj]
  erw [F.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc,
    F.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  rw [mapDerivedCategoryFactorsh_hom_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [DerivedCategory.Q_obj_single_obj, map_comp, comp_obj, map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.assoc, mapDerivedCategorySingleFunctor, Iso.trans_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom, isoWhiskerLeft_inv, NatTrans.comp_app,
    whiskerRight_app, associator_hom_app, whiskerLeft_app, associator_inv_app,
    NatIso.cancel_natIso_hom_left]
  erw [Functor.map_id, Category.id_comp]


/-- On a flat object, the two canonical identifications for an exact functor coincide. -/
lemma leftDerivedFunctorSingleFunctorIsoOfFlat_hom_eq_exact
    {P : C} (hP : ObjectProperty.flat P) :
    (F.leftDerivedFunctorSingleFunctorIsoOfFlat hP).hom =
      F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.singleFunctor C 0).obj P) ≫
        (F.mapDerivedCategorySingleFunctor 0).hom.app P := by
  rw [← puritySingleComparison_app_eq_of_flat, puritySingleComparison_app_eq_exact]

end CategoryTheory.Functor
