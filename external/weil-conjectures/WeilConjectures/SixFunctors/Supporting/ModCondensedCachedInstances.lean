/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Cached instances for module objects over `Λ_Z`

Every derived functor of module objects over `Λ_Z = condensedRingObj Λ Z`, such as
`L((f)^*⟦Λ⟧)` (`Functor.leftDerivedFunctor`), carries the instance arguments below for the
category `Mod (Sheaf (ProEt.topology Z) Ab) (condensedRingObj Λ Z)`. The generic search for the
`∀`-quantified graded tensor instances and the `ℤ`-colimit instances takes 1-4 s per use, and it
is not cached across declarations. A module that uses these derived functors many times can
import this file and open the scope
`AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances`, so that each instance is found at
once. Every instance is `inferInstance`.

The instances are scoped (2026-10-27): seen by every module downstream of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, their unification against
other rings defined as `condensedRingObj` (such as `AlgebraicGeometry.ProEtale.AdicCompletion.ring`)
made instance searches there time out
(`WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperReductionBound`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (Z : Scheme.{u})

scoped instance (priority := 2000) cached_hasTensor₄ObjExt
    (A B C D : GradedObject ℤ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    GradedObject.HasTensor₄ObjExt A B C D :=
  inferInstance

scoped instance (priority := 2000) cached_hasGoodTensor₁₂Tensor
    (A B C : GradedObject ℤ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    GradedObject.HasGoodTensor₁₂Tensor A B C :=
  inferInstance

scoped instance (priority := 2000) cached_hasGoodTensorTensor₂₃
    (A B C : GradedObject ℤ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    GradedObject.HasGoodTensorTensor₂₃ A B C :=
  inferInstance

scoped instance (priority := 2000) cached_hasColimitsOfShape_int :
    HasColimitsOfShape ℤ
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

scoped instance (priority := 2000) cached_hasExactColimitsOfShape_int :
    HasExactColimitsOfShape ℤ
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

scoped instance (priority := 2000) cached_hasCountableCoproducts :
    HasCountableCoproducts
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

scoped instance (priority := 2000) cached_preservesColimitsOfShape_int_tensorLeft
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) :=
  inferInstance

scoped instance (priority := 2000) cached_preservesColimitsOfShape_int_tensorRight
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) :=
  inferInstance

scoped instance (priority := 2000) cached_hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

scoped instance (priority := 2000) cached_hasTensor
    (A B : GradedObject ℤ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    GradedObject.HasTensor A B :=
  inferInstance

scoped instance (priority := 2000) cached_preservesColimit_empty_tensorLeft
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimit (Functor.empty.{0} _) ((curriedTensor _).obj M) :=
  inferInstance

scoped instance (priority := 2000) cached_preservesColimit_empty_tensorRight
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimit (Functor.empty.{0} _) ((curriedTensor _).flip.obj M) :=
  inferInstance

scoped instance (priority := 2000) cached_preservesZeroMorphisms_tensorLeft
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    ((curriedTensor _).obj M).PreservesZeroMorphisms :=
  inferInstance

scoped instance (priority := 2000) cached_preservesZeroMorphisms_tensorRight
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    ((curriedTensor _).flip.obj M).PreservesZeroMorphisms :=
  inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
