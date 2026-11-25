/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeModelNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.DerivedModelNormalizations
import WeilConjectures.Tactic.ExactModProofs

/-! # Native realization preserves the family of tensor models -/

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
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The native realization normalization, packaged for the whole family of flat models. -/
lemma projection_native_realization_model_normalization :
    ProjectionRealizationModelNormalization (condensedRealization k₀ l X)
      (nativeTensorTotal k₀ l X) (nativeDerivedTensor k₀ l X) (NativeIsKFlat k₀ l X)
      (nativeOpenTensorModel k₀ l X) (condensedRealizationTotalTensorIso k₀ l X)
      (condensedRealizationTensor k₀ l X) := by
  intro P T hP hT
  have h := projection_condensed_model_normalization k₀ l X P T hP hT
  dsimp only [derivedCondensedRealization, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj, curriedTensor_obj_obj, MonoidalCategory.tensor_obj, Iso.app] at h ⊢
  dsimp only [Mod.monoidalCategoryCochainComplex, HomologicalComplex.monoidalCategory,
    Monoidal.induced, HomologicalComplex.monoidalCategoryStruct,
    HomologicalComplex.tensorObj, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex] at h ⊢
  with_reducible_and_instances cast_proofs h

end AlgebraicGeometry.ProEtaleWeilSheaf
