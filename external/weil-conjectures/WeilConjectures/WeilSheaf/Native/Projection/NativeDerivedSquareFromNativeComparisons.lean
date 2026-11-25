/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromNativeRestriction
public import WeilConjectures.WeilSheaf.Native.Projection.NativeModelFamilyNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances

/-! # Localization with the native restriction and realization comparisons -/

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
  (R :
      (Mod (Sheaf (Scheme.ProEt.topology
          (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀)))) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k₀))))) ⥤
      (Mod (Sheaf (Scheme.ProEt.topology
          (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀)))) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiber (Z ↘ Spec (CommRingCat.of k₀))))))
  [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- Fix all native comparisons and their normalizations, with the geometric functor abstract. -/
lemma projection_derived_square_of_native_comparisons
    (e : (upperStar k₀ l g) ⋙ (condensedRealization k₀ l Z) ≅ (condensedRealization k₀ l Y) ⋙ R)
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
      ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ))
          ((condensedRealization k₀ l Z).mapHomologicalComplex (.up ℤ))
      ((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ))
          (R.mapHomologicalComplex (.up ℤ))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) (nativePullTotalTensor k₀ l g)
          (condensedRealizationTotalTensorIso k₀ l Y) (condensedRealizationTotalTensorIso k₀ l Z)
      (projection_model_complex_square (upperStar k₀ l g) (condensedRealization k₀ l Z)
          (condensedRealization k₀ l Y) R e).symm
      (fun X Y ↦ (d X Y).hom) P T) :
    PullTensorSquareWithComparison (upperStar k₀ l g).mapDerivedCategory
      (condensedRealization k₀ l Z).mapDerivedCategory
          (condensedRealization k₀ l Y).mapDerivedCategory
      R.mapDerivedCategory (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
      (nativePullTensor k₀ l g) (condensedRealizationTensor k₀ l Y)
          (condensedRealizationTensor k₀ l Z) (Functor.mapDerivedCategorySquareIso e).symm cmp
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  exact projection_derived_square_of_native_restriction k₀ l g
    (condensedRealization k₀ l Z) (condensedRealization k₀ l Y) R e
    (condensedRealizationTensor k₀ l Y) (condensedRealizationTensor k₀ l Z)
    (condensedRealizationTotalTensorIso k₀ l Y) (condensedRealizationTotalTensorIso k₀ l Z)
    (projection_native_realization_model_normalization k₀ l Y)
    (projection_native_realization_model_normalization k₀ l Z)
    d cmp ho P T hP hT htotal

end AlgebraicGeometry.ProEtaleWeilSheaf
