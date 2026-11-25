/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac

/-! # Naturality of the comparison with a complex concentrated in degree zero -/

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

/-- The comparison from the derived image of an object in degree zero to the ordinary
image in degree zero. It is defined for every object, and is invertible on flat objects. -/
noncomputable def puritySingleComparison :
    DerivedCategory.singleFunctor C 0 ⋙ L(F) ⟶ F ⋙ DerivedCategory.singleFunctor D 0 :=
  whiskerRight ((DerivedCategory.singleFunctorIsoCompQ C 0).hom ≫
      whiskerLeft (HomologicalComplex.single C (.up ℤ) 0)
        (DerivedCategory.quotientCompQhIso C).inv) L(F) ≫
    whiskerLeft (HomologicalComplex.single C (.up ℤ) 0 ⋙ HomotopyCategory.quotient C (.up ℤ))
      F.leftDerivedFunctorCounit ≫
    whiskerLeft (HomologicalComplex.single C (.up ℤ) 0)
      (whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh) ≫
    whiskerLeft (HomologicalComplex.single C (.up ℤ) 0 ⋙ F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).hom ≫
    whiskerRight (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom
      DerivedCategory.Q ≫
    whiskerLeft F (DerivedCategory.singleFunctorIsoCompQ D 0).inv

lemma puritySingleComparison_app_eq_of_flat {P : C} (hP : ObjectProperty.flat P) :
    F.puritySingleComparison.app P = (F.leftDerivedFunctorSingleFunctorIsoOfFlat hP).hom := by
  simp only [puritySingleComparison, leftDerivedFunctorSingleFunctorIsoOfFlat,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, asIso_hom, Functor.map_comp,
    Category.assoc, Functor.comp_obj]

/-- The flat-object comparison is natural in maps between flat objects. -/
lemma leftDerivedFunctorSingleFunctorIsoOfFlat_naturality
    {P Q : C} (hP : ObjectProperty.flat P) (hQ : ObjectProperty.flat Q) (s : P ⟶ Q) :
    L(F).map ((DerivedCategory.singleFunctor C 0).map s) ≫
        (F.leftDerivedFunctorSingleFunctorIsoOfFlat hQ).hom =
      (F.leftDerivedFunctorSingleFunctorIsoOfFlat hP).hom ≫
        (DerivedCategory.singleFunctor D 0).map (F.map s) := by
  simpa only [Functor.comp_map, puritySingleComparison_app_eq_of_flat F hP,
    puritySingleComparison_app_eq_of_flat F hQ] using F.puritySingleComparison.naturality s

end CategoryTheory.Functor
