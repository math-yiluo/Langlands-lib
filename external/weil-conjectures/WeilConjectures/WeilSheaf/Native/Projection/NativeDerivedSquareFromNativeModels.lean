/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromModelFamilies
public import WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances

/-! # Localization with native tensor models and abstract exact functors -/

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

variable
  (L : (ProEtaleWeilSheaf k₀ l Y) ⥤ (ProEtaleWeilSheaf k₀ l Z))
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
  [L.Additive] [V.Additive] [F.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- Specialize the tensor models while keeping the exact functors abstract. In particular the
restriction normalization remains in its named native form. -/
lemma projection_derived_square_of_native_models
    (e : L ⋙ V ≅ F ⋙ R)
    (tz : nativeDerivedTensor k₀ l Y ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory.prod F.mapDerivedCategory ⋙ Functor.uncurry.obj (curriedTensor _))
    (tu : nativeDerivedTensor k₀ l Z ⋙ V.mapDerivedCategory ≅
      V.mapDerivedCategory.prod V.mapDerivedCategory ⋙ Functor.uncurry.obj (curriedTensor _))
    (rho : nativeDerivedTensor k₀ l Y ⋙ L.mapDerivedCategory ≅
      L.mapDerivedCategory.prod L.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l Z)
    (hL : ∀ P, NativeIsKFlat k₀ l Y P →
      NativeIsKFlat k₀ l Z ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙
        L.mapHomologicalComplex (.up ℤ) ≅
      (L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
    (nY : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙
        F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _))
    (nZ : Functor.uncurry.obj (nativeTensorTotal k₀ l Z) ⋙
        V.mapHomologicalComplex (.up ℤ) ≅
      (V.mapHomologicalComplex (.up ℤ)).prod (V.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor _))
    (hn : ProjectionRestrictionTensorNormalization k₀ l L hL t rho)
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
      (L.mapHomologicalComplex (.up ℤ)) (V.mapHomologicalComplex (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) t nY nZ
      (projection_model_complex_square L V F R e).symm
      (fun X Y ↦ (d X Y).hom) P T) :
    PullTensorSquareWithComparison L.mapDerivedCategory V.mapDerivedCategory F.mapDerivedCategory
      R.mapDerivedCategory (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
      rho tz tu (Functor.mapDerivedCategorySquareIso e).symm cmp
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  exact projection_derived_square_of_model_families L V F R e
    (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z) tz tu rho
    (nativeTensorTotal k₀ l Y) (nativeTensorTotal k₀ l Z)
    (NativeIsKFlat k₀ l Y) (NativeIsKFlat k₀ l Z) hL
    (nativeOpenTensorModel k₀ l Y) (nativeOpenTensorModel k₀ l Z) t nY nZ
    (by exact hn) hF hV d cmp ho P T hP hT htotal

end AlgebraicGeometry.ProEtaleWeilSheaf
