/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.EpiMono

/-! # Cancelling the normalized model in a tensor square -/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- Map a three-step equality without simplifying concrete functor expressions. -/
lemma Functor.projection_map_comp3_eq (F : C ⥤ D)
    {X Y A B A' B' : C}
    {a : X ⟶ A} {b : A ⟶ B} {c : B ⟶ Y}
    {a' : X ⟶ A'} {b' : A' ⟶ B'} {c' : B' ⟶ Y}
    (h : a ≫ b ≫ c = a' ≫ b' ≫ c') :
    F.map a ≫ F.map b ≫ F.map c = F.map a' ≫ F.map b' ≫ F.map c' := by
  simpa only [Functor.map_comp] using F.congr_map h

/-- Paste a model normalization with its image under a functor. -/
lemma Functor.projection_map_model_square (F : C ⥤ D)
    {A B E : C} {U V W : D}
    {m : A ⟶ B} {a : A ⟶ E} {b : E ⟶ B}
    {r : F.obj B ⟶ U} {s : U ⟶ W} {d : F.obj E ⟶ V} {n q : V ⟶ W}
    (hm : m = a ≫ b) (hn : n = q) (ho : d ≫ q = F.map b ≫ r ≫ s) :
    F.map m ≫ r ≫ s = F.map a ≫ d ≫ n := by
  rw [hm, F.map_comp, Category.assoc, ← ho, hn]

/-- Cancel a common invertible model after pasting the ordinary tensor square. -/
lemma projection_cancel_model_square
    {A₀ A₁ A₂ A₃ B₁ B₂ B₃ B₄ W : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {n : A₃ ⟶ W} [Mono n]
    {d : A₀ ⟶ B₁} {r : B₁ ⟶ B₂} {s : B₂ ⟶ B₃} {t : B₃ ⟶ W}
    {e : B₁ ⟶ B₄} {f : B₄ ⟶ A₃}
    (h : a ≫ b ≫ c ≫ n = d ≫ r ≫ s ≫ t)
    (hr : r ≫ s ≫ t = e ≫ f ≫ n) : a ≫ b ≫ c = d ≫ e ≫ f := by
  apply (cancel_mono n).1
  simpa only [Category.assoc, hr] using h

end CategoryTheory
