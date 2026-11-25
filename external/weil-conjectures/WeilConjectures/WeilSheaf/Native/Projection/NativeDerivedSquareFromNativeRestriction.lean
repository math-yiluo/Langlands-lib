/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromNativeModels
public import WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances

/-! # Localization with the native restriction comparison -/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing
universe u
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf
open ProEtale
attribute [local instance] projection_hasSmallColimits projection_hasTensor
  projection_nativeHasTotal projection_tensorLeftPreservesInitial
  projection_tensorRightPreservesInitial projection_hasGoodTensor12
  projection_hasGoodTensor23 projection_hasTensor4Ext

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]

variable (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

variable
  (V : (ProEtaleWeilSheaf k₀ l Z) ⥤
      (Mod (Sheaf (Scheme.ProEt.topology
          (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀)))) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀))))))
  (F : (ProEtaleWeilSheaf k₀ l Y) ⥤
      (Mod (Sheaf (Scheme.ProEt.topology
          (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀)))) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀))))))
  (R :
      (Mod (Sheaf (Scheme.ProEt.topology
          (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀)))) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀))))) ⥤
      (Mod (Sheaf (Scheme.ProEt.topology
          (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀)))) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀))))))
  [V.Additive] [F.Additive] [R.Additive]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- Fix native restriction and its normalization while retaining abstract realization functors. -/
lemma projection_derived_square_of_native_restriction
    (e : (upperStar k₀ l g) ⋙ V ≅ F ⋙ R)
    (tz : nativeDerivedTensor k₀ l Y ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory.prod F.mapDerivedCategory ⋙ Functor.uncurry.obj (curriedTensor _))
    (tu : nativeDerivedTensor k₀ l Z ⋙ V.mapDerivedCategory ≅
      V.mapDerivedCategory.prod V.mapDerivedCategory ⋙ Functor.uncurry.obj (curriedTensor _))
    (nY : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙
        F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _))
    (nZ : Functor.uncurry.obj (nativeTensorTotal k₀ l Z) ⋙
        V.mapHomologicalComplex (.up ℤ) ≅
      (V.mapHomologicalComplex (.up ℤ)).prod (V.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _))
    (hF : ProjectionRealizationModelNormalization F (nativeTensorTotal k₀ l Y)
      (nativeDerivedTensor k₀ l Y) (NativeIsKFlat k₀ l Y) (nativeOpenTensorModel k₀ l Y) nY tz)
    (hV : ProjectionRealizationModelNormalization V (nativeTensorTotal k₀ l Z)
      (nativeDerivedTensor k₀ l Z) (NativeIsKFlat k₀ l Z) (nativeOpenTensorModel k₀ l Z) nZ tu)
    (d : ∀ X Y : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology
            (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀)))) Ab)
          (condensedRingObj (Profinite.padicAlgClRingObj l)
            (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀))))) ℤ,
      (R.mapHomologicalComplex (.up ℤ)).obj (X ⊗ Y) ≅
        (R.mapHomologicalComplex (.up ℤ)).obj X ⊗ (R.mapHomologicalComplex (.up ℤ)).obj Y)
    (cmp : ∀ X Y : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology
            (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀)))) Ab)
          (condensedRingObj (Profinite.padicAlgClRingObj l)
            (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀))))),
      R.mapDerivedCategory.obj (X ⊗ Y) ⟶
        R.mapDerivedCategory.obj X ⊗ R.mapDerivedCategory.obj Y)
    (ho : ProjectionOrdinaryModelNormalization R d cmp)
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : NativeIsKFlat k₀ l Y P) (hT : NativeIsKFlat k₀ l Y T)
    (htotal : PullTensorSquareWithComparison
      ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) (nativePullTotalTensor k₀ l g) nY nZ
      (projection_model_complex_square (upperStar k₀ l g) V F R e).symm
      (fun X Y ↦ (d X Y).hom) P T) :
    PullTensorSquareWithComparison (upperStar k₀ l g).mapDerivedCategory
      V.mapDerivedCategory F.mapDerivedCategory
      R.mapDerivedCategory (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
      (nativePullTensor k₀ l g) tz tu (Functor.mapDerivedCategorySquareIso e).symm cmp
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  exact projection_derived_square_of_native_models k₀ l (upperStar k₀ l g) V F R e
    tz tu (nativePullTensor k₀ l g)
    (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g)
    (nativePullTotalTensor k₀ l g) nY nZ
    (projection_nativePullTensor_normalization k₀ l g)
    hF hV d cmp ho P T hP hT htotal

end AlgebraicGeometry.ProEtaleWeilSheaf
