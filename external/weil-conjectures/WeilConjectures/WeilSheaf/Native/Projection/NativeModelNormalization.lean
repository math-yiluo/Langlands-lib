/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
import WeilConjectures.Tactic.ExactModProofs

/-! # The native condensed tensor model in localization notation -/

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

/-- Write realization of the native model using the localization tensorator. -/
lemma projection_condensed_model_normalization
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) (hT : NativeIsKFlat k₀ l X T) :
    let F := condensedRealization k₀ l X
    F.mapDerivedCategory.map (nativeOpenTensorModel k₀ l X P T hP hT).hom ≫
      F.mapDerivedCategoryFactors.hom.app (((nativeTensorTotal k₀ l X).obj P).obj T) ≫
        DerivedCategory.Q.map ((condensedRealizationTotalTensorIso k₀ l X).app (P, T)).hom =
    (condensedRealizationTensor k₀ l X).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj T) := by
  have h := (condensedRealizationTensor_hom_app_comp k₀ l X P T hP hT).symm
  dsimp only
  simp only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
    ← MonoidalCategory.tensorHom_def, Iso.app_hom, condensedTensorModel,
    asIso_hom] at h ⊢
  dsimp only [derivedCondensedRealization, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj, curriedTensor_obj_obj, MonoidalCategory.tensor_obj] at h ⊢
  dsimp only [Mod.monoidalCategoryCochainComplex, HomologicalComplex.monoidalCategory,
    Monoidal.induced, HomologicalComplex.monoidalCategoryStruct,
    HomologicalComplex.tensorObj, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex] at h ⊢
  with_reducible_and_instances cast_proofs h

end AlgebraicGeometry.ProEtaleWeilSheaf
