/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.NativePullTensor
import WeilConjectures.Tactic.ExactModProofs

/-! # Normalization of the native pullback tensor comparison -/

@[expose] public noncomputable section

set_option Elab.async false

-- Match the coefficient-category instance used to construct nativePullTensor.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

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
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- Form the normalization proposition with the exact functor and comparisons abstract. -/
def ProjectionRestrictionTensorNormalization
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
    (rho : nativeDerivedTensor k₀ l Y ⋙ R.mapDerivedCategory ≅
      R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l Z) : Prop :=
  OpenTensorRestrictionNormalization R
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
    (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
    (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
    (NativeRestrictionDescentProof.totalFamily R
      (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y) t) rho

/-- Normalize descent while keeping its exact functor and total comparison abstract. -/
lemma projection_nativeRestrictionDerivedTensor_normalization
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) :
    ProjectionRestrictionTensorNormalization k₀ l R hR t
      (nativeRestrictionDerivedTensor k₀ l R hR t) := by
  have := native_open_tensor_full_kflat_localization k₀ l Y
  unfold ProjectionRestrictionTensorNormalization nativeRestrictionDerivedTensor
  exact_mod_proofs NativeRestrictionDescentProof.restrictionDerivedOfTotal_normalization
    R (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
    (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
    (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
    (nativeOpenTensorModel_naturality k₀ l Z) (nativeOpenTensorModel_naturality k₀ l Y) t

/-- The normalization of the native pullback tensor comparison on K-flat complexes. -/
lemma projection_nativePullTensor_normalization :
    ProjectionRestrictionTensorNormalization k₀ l (upperStar k₀ l g)
      (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g)
      (nativePullTotalTensor k₀ l g) (nativePullTensor k₀ l g) := by
  have h := projection_nativeRestrictionDerivedTensor_normalization k₀ l _
    (by
      intro T hT
      cast_proofs nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g T hT)
    (nativePullTotalTensor k₀ l g)
  dsimp only [nativePullTensor]
  exact_mod_proofs h

end AlgebraicGeometry.ProEtaleWeilSheaf
