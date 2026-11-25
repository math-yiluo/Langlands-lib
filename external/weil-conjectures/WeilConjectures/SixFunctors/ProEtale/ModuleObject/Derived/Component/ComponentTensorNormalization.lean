/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentFreeTensorDetection
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Monoidal.Multifunctor
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

set_option linter.privateModule false

/-! # Unit normalization of the component inverse image

Source: Hemo--Richarz--Scholbach, Construction (4.1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Prod
private theorem tensor_naturality
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (α : curriedTensorPre F ⟶ curriedTensorPost F)
    {X Y X' Y' : C} (a : X ⟶ X') (b : Y ⟶ Y') :
    (F.map a ⊗ₘ F.map b) ≫ (α.app X').app Y' =
      (α.app X).app Y ≫ F.map (a ⊗ₘ b) := by
  have h := (Functor.uncurry.map α).naturality (a ×ₘ b)
  change (F.map a ▷ F.obj Y ≫ F.obj X' ◁ F.map b) ≫ _ =
    _ ≫ (F.map (a ▷ Y) ≫ F.map (X' ◁ b)) at h
  dsimp only [Functor.uncurry] at h
  simpa only [← MonoidalCategory.tensorHom_def, ← F.map_comp] using h

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]

variable [(componentInverse T).Braided]

end AlgebraicGeometry.ProEtale.CondensedRing
