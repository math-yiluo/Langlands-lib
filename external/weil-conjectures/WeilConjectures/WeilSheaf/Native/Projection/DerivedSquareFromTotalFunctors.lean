/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromModels

/-! # Derived tensor squares from natural total-model comparisons -/

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

/-- Form the total-model components over abstract categories before specializing the square. -/
lemma projection_derived_square_of_total_functors
    (e : L ⋙ V ≅ F ⋙ R)
    (DZ : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C)
    (DU : DerivedCategory D × DerivedCategory D ⥤ DerivedCategory D)
    (tz : DZ ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
      Functor.uncurry.obj (curriedTensor _))
    (tu : DU ⋙ V.mapDerivedCategory ≅ V.mapDerivedCategory.prod V.mapDerivedCategory ⋙
      Functor.uncurry.obj (curriedTensor _))
    (rho : DZ ⋙ L.mapDerivedCategory ≅
      L.mapDerivedCategory.prod L.mapDerivedCategory ⋙ DU)
    (TC : CochainComplex C ℤ × CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (TD : CochainComplex D ℤ × CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (t : TC ⋙ L.mapHomologicalComplex (.up ℤ) ≅
      (L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ)) ⋙ TD)
    (nY : TC ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _))
    (nZ : TD ⋙ V.mapHomologicalComplex (.up ℤ) ≅
      (V.mapHomologicalComplex (.up ℤ)).prod (V.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _))
    (P T : CochainComplex C ℤ)
    (modelZ : DZ.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj (TC.obj (P, T)))
    (modelU : DU.obj
        (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P),
          DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj T)) ≅
      DerivedCategory.Q.obj (TD.obj
        (((L.mapHomologicalComplex (.up ℤ)).obj P),
          ((L.mapHomologicalComplex (.up ℤ)).obj T))))
    (hr : V.mapDerivedCategory.map
          (rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        V.mapDerivedCategory.map
          (DU.map (Prod.mkHom (L.mapDerivedCategoryFactors.hom.app P)
            (L.mapDerivedCategoryFactors.hom.app T))) ≫
        V.mapDerivedCategory.map modelU.hom =
      V.mapDerivedCategory.map (L.mapDerivedCategory.map modelZ.hom) ≫
        V.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app (TC.obj (P, T))) ≫
        V.mapDerivedCategory.map (DerivedCategory.Q.map (t.app (P, T)).hom))
    (hmU : V.mapDerivedCategory.map modelU.hom ≫
        V.mapDerivedCategoryFactors.hom.app (TD.obj
          (((L.mapHomologicalComplex (.up ℤ)).obj P),
            ((L.mapHomologicalComplex (.up ℤ)).obj T))) ≫
        DerivedCategory.Q.map (nZ.app
          (((L.mapHomologicalComplex (.up ℤ)).obj P),
            ((L.mapHomologicalComplex (.up ℤ)).obj T))).hom =
      tu.hom.app
          (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P),
            DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj T)) ≫
        (V.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ⊗ₘ
          V.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj T)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((V.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj P))
          ((V.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj T)))
    (d : ∀ X Y : CochainComplex A ℤ,
      (R.mapHomologicalComplex (.up ℤ)).obj (X ⊗ Y) ≅
        (R.mapHomologicalComplex (.up ℤ)).obj X ⊗ (R.mapHomologicalComplex (.up ℤ)).obj Y)
    (htotal : PullTensorSquareWithComparison
      (L.mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ))
      TC TD t nY nZ (projection_model_complex_square L V F R e).symm
      (fun X Y ↦ (d X Y).hom) P T)
    (hmZ : F.mapDerivedCategory.map modelZ.hom ≫
        F.mapDerivedCategoryFactors.hom.app (TC.obj (P, T)) ≫ DerivedCategory.Q.map
            (nY.app (P, T)).hom =
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
            (F.mapHomologicalComplex (.up ℤ)).obj T) ≫
        DerivedCategory.Q.map (d ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj T)).hom) :
    PullTensorSquareWithComparison L.mapDerivedCategory V.mapDerivedCategory F.mapDerivedCategory
      R.mapDerivedCategory DZ DU rho tz tu (Functor.mapDerivedCategorySquareIso e).symm cmp
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  exact projection_derived_square_of_total_models L V F R e DZ DU tz tu rho P T
    (TC.obj (P, T)) (TD.obj (((L.mapHomologicalComplex (.up ℤ)).obj P),
      ((L.mapHomologicalComplex (.up ℤ)).obj T))) modelZ modelU
    (t.app (P, T)) hr (nY.app (P, T)) (nZ.app
      (((L.mapHomologicalComplex (.up ℤ)).obj P),
        ((L.mapHomologicalComplex (.up ℤ)).obj T))) hmU
    (d ((F.mapHomologicalComplex (.up ℤ)).obj P) ((F.mapHomologicalComplex (.up ℤ)).obj T))
    (projection_model_square_from_tensor_square
      (L.mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ))
      TC TD t nY nZ (projection_model_complex_square L V F R e) d P T htotal)
    hmZ cmp ho

end AlgebraicGeometry.ProEtaleWeilSheaf
