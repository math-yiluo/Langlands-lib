/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromTotalFunctors
public import WeilConjectures.WeilSheaf.Native.Projection.DerivedModelNormalizations
public import WeilConjectures.WeilSheaf.Native.NativePullTensor

/-! # Localizing tensor squares using whole families of flat models -/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.ProEtaleWeilSheaf
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u v

variable {C D A B : Type u} [Category.{v} C] [Category.{v} D]
  [Category.{v} A] [Category.{v} B]
  [Abelian C] [Abelian D] [Abelian A] [Abelian B]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D]
  [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
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

/-- The total square localizes when restriction and realization preserve the chosen flat models. -/
lemma projection_derived_square_of_model_families
    (e : L ⋙ V ≅ F ⋙ R)
    (DZ : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C)
    (DU : DerivedCategory D × DerivedCategory D ⥤ DerivedCategory D)
    (tz : DZ ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
      Functor.uncurry.obj (curriedTensor _))
    (tu : DU ⋙ V.mapDerivedCategory ≅ V.mapDerivedCategory.prod V.mapDerivedCategory ⋙
      Functor.uncurry.obj (curriedTensor _))
    (rho : DZ ⋙ L.mapDerivedCategory ≅
      L.mapDerivedCategory.prod L.mapDerivedCategory ⋙ DU)
    (TC : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (TD : CochainComplex D ℤ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (flatC : CochainComplex C ℤ → Prop) (flatD : CochainComplex D ℤ → Prop)
    (hL : ∀ P, flatC P → flatD ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (modelC : ∀ P T, flatC P → flatC T →
      (DZ.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TC.obj P).obj T)))
    (modelD : ∀ P T, flatD P → flatD T →
      (DU.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TD.obj P).obj T)))
    (t : Functor.uncurry.obj TC ⋙ L.mapHomologicalComplex (.up ℤ) ≅
      (L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TD)
    (nY : Functor.uncurry.obj TC ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _))
    (nZ : Functor.uncurry.obj TD ⋙ V.mapHomologicalComplex (.up ℤ) ≅
      (V.mapHomologicalComplex (.up ℤ)).prod (V.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _))
    (hn : OpenTensorRestrictionNormalization L TD TC DU DZ flatD flatC hL modelD modelC
      (NativeRestrictionDescentProof.totalFamily L TD TC t) rho)
    (hF : ProjectionRealizationModelNormalization F TC DZ flatC modelC nY tz)
    (hV : ProjectionRealizationModelNormalization V TD DU flatD modelD nZ tu)
    (d : ∀ X Y : CochainComplex A ℤ,
      (R.mapHomologicalComplex (.up ℤ)).obj (X ⊗ Y) ≅
        (R.mapHomologicalComplex (.up ℤ)).obj X ⊗ (R.mapHomologicalComplex (.up ℤ)).obj Y)
    (cmp : ∀ X Y : DerivedCategory A,
      R.mapDerivedCategory.obj (X ⊗ Y) ⟶
        R.mapDerivedCategory.obj X ⊗ R.mapDerivedCategory.obj Y)
    (ho : ProjectionOrdinaryModelNormalization R d cmp)
    (P T : CochainComplex C ℤ) (hP : flatC P) (hT : flatC T)
    (htotal : PullTensorSquareWithComparison
      (L.mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ))
      (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) t nY nZ
      (projection_model_complex_square L V F R e).symm
      (fun X Y ↦ (d X Y).hom) P T) :
    PullTensorSquareWithComparison L.mapDerivedCategory V.mapDerivedCategory F.mapDerivedCategory
      R.mapDerivedCategory DZ DU rho tz tu (Functor.mapDerivedCategorySquareIso e).symm cmp
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  exact projection_derived_square_of_total_functors L V F R e DZ DU tz tu rho
    (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) t nY nZ P T
    (modelC P T hP hT)
    (modelD ((L.mapHomologicalComplex (.up ℤ)).obj P)
      ((L.mapHomologicalComplex (.up ℤ)).obj T) (hL P hP) (hL T hT))
    (V.mapDerivedCategory.projection_map_comp3_eq (hn P T hP hT))
    (hV _ _ (hL P hP) (hL T hT)) d htotal (hF P T hP hT) cmp
    (ho (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
      (F.mapDerivedCategory.obj (DerivedCategory.Q.obj T))
      ((F.mapHomologicalComplex (.up ℤ)).obj P) ((F.mapHomologicalComplex (.up ℤ)).obj T)
      (F.mapDerivedCategoryFactors.hom.app P) (F.mapDerivedCategoryFactors.hom.app T))

end AlgebraicGeometry.ProEtaleWeilSheaf
