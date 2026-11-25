/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Underlying maps of the mapped-module unit comparison -/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [HasCoequalizers D] [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (F : C ⥤ D) [F.Braided]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- Postcomposing a trivialization with the mapped unit does not change its underlying map. -/
lemma purity_mapModUnitIso_postcompose_hom
    {M : Mod D (F.obj R)} (e : M ≅ 𝟙_ (Mod D (F.obj R))) :
    (e ≪≫ F.mapModUnitIso).hom.hom = e.hom.hom := by
  change e.hom.hom ≫ 𝟙 _ = e.hom.hom
  exact Category.comp_id _

end CategoryTheory
