/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.OrdinaryTensorNormalization
public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorPresentation

/-! # Model normalizations as families over abstract coefficient categories -/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

/-- Realization carries every chosen flat tensor model to the localization tensorator. -/
def ProjectionRealizationModelNormalization
    {C A : Type*} [Category* C] [Category* A] [Abelian C] [Abelian A]
    [HasDerivedCategory C] [HasDerivedCategory A]
    [MonoidalCategory (CochainComplex A ℤ)] [MonoidalCategory (DerivedCategory A)]
    [Functor.LaxMonoidal (DerivedCategory.Q (C := A))]
    (F : C ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (TC : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (DC : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C)
    (flat : CochainComplex C ℤ → Prop)
    (model : ∀ P T, flat P → flat T →
      (DC.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TC.obj P).obj T)))
    (n : Functor.uncurry.obj TC ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _))
    (tau : DC ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory.prod F.mapDerivedCategory ⋙ Functor.uncurry.obj (curriedTensor _)) :
    Prop :=
  ∀ P T (hP : flat P) (hT : flat T),
    F.mapDerivedCategory.map (model P T hP hT).hom ≫
      F.mapDerivedCategoryFactors.hom.app ((TC.obj P).obj T) ≫
        DerivedCategory.Q.map (n.app (P, T)).hom =
    tau.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj T)

/-- Normalization of an ordinary tensor comparison against arbitrary localized models. -/
def ProjectionOrdinaryModelNormalization
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [MonoidalCategory (CochainComplex A ℤ)] [MonoidalCategory (CochainComplex B ℤ)]
    [MonoidalCategory (DerivedCategory A)] [MonoidalCategory (DerivedCategory B)]
    [Functor.LaxMonoidal (DerivedCategory.Q (C := A))]
    [Functor.LaxMonoidal (DerivedCategory.Q (C := B))]
    (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (d : ∀ P T : CochainComplex A ℤ,
      (R.mapHomologicalComplex (.up ℤ)).obj (P ⊗ T) ≅
        (R.mapHomologicalComplex (.up ℤ)).obj P ⊗ (R.mapHomologicalComplex (.up ℤ)).obj T)
    (cmp : ∀ X Y : DerivedCategory A,
      R.mapDerivedCategory.obj (X ⊗ Y) ⟶
        R.mapDerivedCategory.obj X ⊗ R.mapDerivedCategory.obj Y) : Prop :=
  ∀ (X Y : DerivedCategory A) (P T : CochainComplex A ℤ)
    (f : X ⟶ DerivedCategory.Q.obj P) (g : Y ⟶ DerivedCategory.Q.obj T),
    cmp X Y ≫
      ((R.mapDerivedCategory.map f ≫ R.mapDerivedCategoryFactors.hom.app P) ⊗ₘ
        (R.mapDerivedCategory.map g ≫ R.mapDerivedCategoryFactors.hom.app T)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((R.mapHomologicalComplex (.up ℤ)).obj P)
          ((R.mapHomologicalComplex (.up ℤ)).obj T) =
      R.mapDerivedCategory.map ((f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ DerivedCategory.Q P T) ≫
        R.mapDerivedCategoryFactors.hom.app (P ⊗ T) ≫ DerivedCategory.Q.map (d P T).hom

universe u u₁ u₂

namespace Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [R.PreservesFlat] [R.IsLeftAdjoint] [R.Monoidal]

/-- The ordinary exact-derived tensor comparison is normalized on every total model. -/
lemma projection_ordinary_model_normalization :
    ProjectionOrdinaryModelNormalization R (fun P T ↦ (R.mapCochainComplexμIso P T).symm)
      (fun X Y ↦ (R.mapDerivedCategoryTensorComparison.app X).app Y) := by
  intro X Y P T f g
  exact R.projection_mapDerivedCategoryTensorComparison_total_model X Y P T f g

end Functor
end CategoryTheory
