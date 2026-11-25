/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.CountableTotalExistence
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTotalSquareStatement

/-! # Colimit interfaces for the native and condensed tensor totalizations -/

@[expose] public noncomputable section

attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf
open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

local instance projection_hasSmallColimits (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] :
    HasColimitsOfSize.{0, 0}
      (Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :=
  hasColimitsOfSizeShrink _

local instance projection_hasTensor (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (A B : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))) : A.HasTensor B :=
  GradedObject.projection_hasCountableMap _ _

local instance projection_nativeHasTotal (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    HomologicalComplex.HasMapBifunctor P T (nativeTensorBifunctor k₀ l X).flip (.up ℤ) :=
  GradedObject.projection_hasCountableMap _ _

local instance projection_tensorLeftPreservesInitial (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (M : Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :
    PreservesColimit (Functor.empty.{0} _) ((curriedTensor _).obj M) :=
  Functor.preservesInitialObject_of_preservesZeroMorphisms _

local instance projection_tensorRightPreservesInitial (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (M : Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :
    PreservesColimit (Functor.empty.{0} _) ((curriedTensor _).flip.obj M) :=
  Functor.preservesInitialObject_of_preservesZeroMorphisms _


local instance projection_hasGoodTensor12 (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := by
  infer_instance

local instance projection_hasGoodTensor23 (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := by
  infer_instance

local instance projection_hasTensor4Ext (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (A B C D : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab)
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))) :
    GradedObject.HasTensor₄ObjExt A B C D := by
  infer_instance

end AlgebraicGeometry.ProEtaleWeilSheaf
