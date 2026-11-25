/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Recognising filtered colimits of modules

A cocone over a filtered diagram of modules is a colimit as soon as every element of its point
comes from some stage and every element of a stage which becomes zero in the point already
becomes zero at a later stage (`ModuleCat.isColimitOfFiltered`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable {Λ : Type (u + 1)} [CommRing Λ] {J : Type u} [Category.{u} J] [IsFiltered J]
  {K : J ⥤ ModuleCat.{u + 1} Λ}

/-- The forgetful functor of `ModuleCat.{u + 1} Λ` preserves filtered colimits indexed by
categories in `Type u`. -/
instance preservesFilteredColimitsOfSize_forget_succ :
    PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _

/-- A cocone `t` over a filtered diagram of modules is a colimit if every element of `t.pt`
comes from some stage, and every element of a stage which maps to zero in `t.pt` maps to zero
at a later stage. -/
noncomputable def isColimitOfFiltered (t : Cocone K)
    (hsurj : ∀ y : t.pt, ∃ (j : J) (x : K.obj j), t.ι.app j x = y)
    (hinj : ∀ (j : J) (x : K.obj j), t.ι.app j x = 0 → ∃ (k : J) (f : j ⟶ k), K.map f x = 0) :
    IsColimit t :=
  have : ReflectsColimit K (forget (ModuleCat.{u + 1} Λ)) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  isColimitOfReflects (forget (ModuleCat.{u + 1} Λ))
    (Types.FilteredColimit.isColimitOf' _ _
      (fun y ↦ by
        obtain ⟨j, x, hx⟩ := hsurj y
        exact ⟨j, x, hx.symm⟩)
      (fun j (x y : K.obj j) hxy ↦ by
        obtain ⟨k, f, hf⟩ := hinj j (x - y) (by
          rw [map_sub]
          exact sub_eq_zero.2 hxy)
        refine ⟨k, f, ?_⟩
        rw [map_sub] at hf
        have h := sub_eq_zero.1 hf
        exact h))

end ModuleCat
