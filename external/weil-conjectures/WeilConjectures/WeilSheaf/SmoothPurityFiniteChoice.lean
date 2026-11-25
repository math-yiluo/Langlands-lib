/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Compatible choices satisfying a reduction-stable condition -/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory

/-- A nonempty finite family of choices at each level admits compatible choices satisfying
any condition preserved by the transitions. -/
theorem exists_compatible_choices_with_property
    {T : ℕ → Type*} (r : ∀ n, T (n + 1) → T n) (P : ∀ n, T n → Prop)
    (hfin : ∀ n, Finite (T n)) (hne : ∀ n, ∃ t, P n t)
    (hr : ∀ n t, P (n + 1) t → P n (r n t)) :
    ∃ t : ∀ n, T n, (∀ n, P n (t n)) ∧ ∀ n, r n (t (n + 1)) = t n := by
  let U (n : ℕ) := {t : T n // P n t}
  let s (n : ℕ) : U (n + 1) → U n := fun t ↦ ⟨r n t.val, hr n t.val t.property⟩
  let F : ℕᵒᵖ ⥤ Type _ := Functor.ofOpSequence (X := U) fun n ↦ TypeCat.ofHom (s n)
  have : ∀ j, Finite (F.obj j) := fun j ↦ by
    have := hfin j.unop
    exact inferInstanceAs (Finite (U j.unop))
  have : ∀ j, Nonempty (F.obj j) := fun j ↦ by
    obtain ⟨t, ht⟩ := hne j.unop
    exact ⟨⟨t, ht⟩⟩
  obtain ⟨t, ht⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n ↦ (t (op n)).val, fun n ↦ (t (op n)).property, fun n ↦ ?_⟩
  have h := ht (homOfLE (Nat.le_add_right n 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg Subtype.val h

end CategoryTheory
