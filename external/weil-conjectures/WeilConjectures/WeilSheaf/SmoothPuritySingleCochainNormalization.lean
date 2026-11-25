/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCochainComparison
public import WeilConjectures.WeilSheaf.SmoothPuritySingleFlatNaturality

/-! # Reading the actual left-derived comparison on complexes in degree zero -/

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

lemma puritySingleComparisonOfCochain_leftDerivedCounit (P : C) :
    (puritySingleComparisonOfCochain F L(F)
      (purityCochainComparisonOfHomotopy F L(F) F.leftDerivedFunctorCounit)).app P =
        F.puritySingleComparison.app P := by
  simp only [puritySingleComparisonOfCochain, purityCochainComparisonOfHomotopy,
    puritySingleComparison, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.map_comp, Category.assoc, Functor.comp_obj]

end CategoryTheory.Functor
