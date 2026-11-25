/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.WeilSheaf.Native.Projection.ModelSquareCancellation
public import WeilConjectures.WeilSheaf.Native.Projection.OrdinaryTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.TotalSquareToModel
import all WeilConjectures.WeilSheaf.Native.NativeRestrictionForgetTotalModel

/-! # Pasting normalized total models before specializing the coefficient categories -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
  [Abelian C] [Abelian D] [Abelian A] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory A] [HasDerivedCategory B]
  [MonoidalCategory (CochainComplex A ℤ)] [MonoidalCategory (CochainComplex B ℤ)]
  [MonoidalCategory (DerivedCategory A)] [MonoidalCategory (DerivedCategory B)]
  [Functor.LaxMonoidal (DerivedCategory.Q (C := A))]
  [Functor.LaxMonoidal (DerivedCategory.Q (C := B))]
  (L : C ⥤ D) (V : D ⥤ B) (F : C ⥤ A) (R : A ⥤ B)
  [L.Additive] [V.Additive] [F.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- The exact-functor square on complexes used by the total models. -/
abbrev projection_model_complex_square (e : L ⋙ V ≅ F ⋙ R) :=
  Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).symm

/-- A square of total models and their normalizations gives the derived tensor square.
All pasting and cancellation take place over abstract coefficient categories. -/
lemma projection_derived_square_of_total_models
    (e : L ⋙ V ≅ F ⋙ R)
    (DZ : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C)
    (DU : DerivedCategory D × DerivedCategory D ⥤ DerivedCategory D)
    (tz : DZ ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
      Functor.uncurry.obj (curriedTensor _))
    (tu : DU ⋙ V.mapDerivedCategory ≅ V.mapDerivedCategory.prod V.mapDerivedCategory ⋙
      Functor.uncurry.obj (curriedTensor _))
    (rho : DZ ⋙ L.mapDerivedCategory ≅
      L.mapDerivedCategory.prod L.mapDerivedCategory ⋙ DU)
    (P T WZ : CochainComplex C ℤ) (WU : CochainComplex D ℤ)
    (modelZ : DZ.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj WZ)
    (modelU : DU.obj
        (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P),
          DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj T)) ≅
      DerivedCategory.Q.obj WU)
    (tr : (L.mapHomologicalComplex (.up ℤ)).obj WZ ≅ WU)
    (hr : V.mapDerivedCategory.map
          (rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        V.mapDerivedCategory.map
          (DU.map (Prod.mkHom (L.mapDerivedCategoryFactors.hom.app P)
            (L.mapDerivedCategoryFactors.hom.app T))) ≫
        V.mapDerivedCategory.map modelU.hom =
      V.mapDerivedCategory.map (L.mapDerivedCategory.map modelZ.hom) ≫
        V.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app WZ) ≫
        V.mapDerivedCategory.map (DerivedCategory.Q.map tr.hom))
    (cZ : (F.mapHomologicalComplex (.up ℤ)).obj WZ ≅
      (F.mapHomologicalComplex (.up ℤ)).obj P ⊗ (F.mapHomologicalComplex (.up ℤ)).obj T)
    (cU : (V.mapHomologicalComplex (.up ℤ)).obj WU ≅
      (V.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj P) ⊗
        (V.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj T))
    (hmU : V.mapDerivedCategory.map modelU.hom ≫
        V.mapDerivedCategoryFactors.hom.app WU ≫ DerivedCategory.Q.map cU.hom =
      tu.hom.app
          (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P),
            DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj T)) ≫
        (V.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ⊗ₘ
          V.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj T)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((V.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj P))
          ((V.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj T)))
    (ord : (R.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P ⊗
          (F.mapHomologicalComplex (.up ℤ)).obj T) ≅
      (R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⊗
        (R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T))
    (hchain : ProjectionTotalModelSquare
      (L.mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ))
      (projection_model_complex_square L V F R e) P T WZ WU tr cZ cU ord)
    (hmZ : F.mapDerivedCategory.map modelZ.hom ≫
        F.mapDerivedCategoryFactors.hom.app WZ ≫ DerivedCategory.Q.map cZ.hom =
      tz.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
        (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj T))
    (cmp : ∀ X Y : DerivedCategory A,
      R.mapDerivedCategory.obj (X ⊗ Y) ⟶
        R.mapDerivedCategory.obj X ⊗ R.mapDerivedCategory.obj Y)
    (ho : cmp (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj T)) ≫
        ((R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
            R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P)) ⊗ₘ
          (R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app T) ≫
            R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj T))) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
          ((R.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T)) =
      R.mapDerivedCategory.map
          ((F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q
              ((F.mapHomologicalComplex (.up ℤ)).obj P)
              ((F.mapHomologicalComplex (.up ℤ)).obj T)) ≫
        R.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P ⊗
            (F.mapHomologicalComplex (.up ℤ)).obj T) ≫ DerivedCategory.Q.map ord.hom) :
    PullTensorSquareWithComparison L.mapDerivedCategory V.mapDerivedCategory F.mapDerivedCategory
      R.mapDerivedCategory DZ DU rho tz tu (Functor.mapDerivedCategorySquareIso e).symm cmp
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  let mZ := F.mapDerivedCategory.mapIso modelZ ≪≫ F.mapDerivedCategoryFactors.app WZ ≪≫
    DerivedCategory.Q.mapIso cZ
  obtain ⟨mU, hmU', hsquare⟩ := final_total_diagram L V F R e DZ DU
    (Functor.uncurry.obj (curriedTensor _)) tu (Functor.projection_uncurryTensorIso _) rho
    P T WZ WU modelZ modelU tr hr cZ cU
    (by
      simp only [Functor.projection_uncurryTensorIso_hom_app, MonoidalCategory.tensor_map,
        Functor.uncurry_obj_obj, curriedTensor_obj_obj]
      erw [Category.id_comp]
      exact hmU) ord
    (by simpa only [ProjectionTotalModelSquare, MonoidalCategory.tensor_map,
      projection_model_complex_square,
      complex_square] using hchain) mZ rfl
  simp only [Functor.projection_uncurryTensorIso_hom_app, Category.id_comp,
    MonoidalCategory.tensor_map, Functor.uncurry_obj_obj, curriedTensor_obj_obj] at hmU'
  simp only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
    ← MonoidalCategory.tensorHom_def] at hsquare
  have hright := R.mapDerivedCategory.projection_map_model_square hmZ hmU' ho
  exact projection_cancel_model_square hsquare hright

end AlgebraicGeometry.ProEtaleWeilSheaf
