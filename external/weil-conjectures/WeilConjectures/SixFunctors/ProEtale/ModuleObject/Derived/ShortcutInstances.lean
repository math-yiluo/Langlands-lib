/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# Shortcuts for the instances of the derived functors on pro-étale module objects

The left derived functor `L(F)` (`Functor.leftDerivedFunctor`) of a functor on the category
`Mod (Sheaf (ProEt.topology T) Ab) R` of module objects over a commutative ring object `R` of
pro-étale abelian sheaves needs the instances
`∀ X₁ X₂ X₃ X₄, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄`,
`∀ X₁ X₂ X₃, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃`,
`∀ X₁ X₂ X₃, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃`, `HasColimitsOfShape ℤ` and the
preservation of colimits of shape `ℤ` by tensoring on either side. The generic search for each of
them takes about a second and is redone at every occurrence of `L(F)` in a statement.

This file states them for every such module category. They are not instances: a file whose
statements contain many derived functors on these categories can make them local instances with
`attribute [local instance]`, which cuts the elaboration of its statements by a factor of 3 to 5.
All of them are propositions, so the statements obtained are the same up to proof irrelevance.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R]
  [IsCommMonObj R]

theorem hasTensor₄ObjExt_mod
    (X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by
  infer_instance

theorem hasGoodTensor₁₂Tensor_mod
    (X₁ X₂ X₃ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by
  infer_instance

theorem hasGoodTensorTensor₂₃_mod
    (X₁ X₂ X₃ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by
  infer_instance

omit [IsCommMonObj R] in
theorem hasColimitsOfShape_int_mod :
    HasColimitsOfShape ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

theorem preservesColimitsOfShape_int_curriedTensor_obj_mod
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) := by
  infer_instance

theorem preservesColimitsOfShape_int_curriedTensor_flip_obj_mod
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) := by
  infer_instance

end AlgebraicGeometry.ProEtale
