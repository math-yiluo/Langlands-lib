/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Transport of a scalar relation through comparison squares -/

@[expose] public section

namespace CategoryTheory

/-- A scalar intertwining relation transports through commuting comparison squares. -/
lemma purity_scalarSquare {C : Type*} [Category C] [Preadditive C]
    {V₀ W₀ V₁ W₁ A₀ B₀ A₁ B₁ : C}
    (u : V₀ ⟶ V₁) [Epi u] (v : W₀ ⟶ W₁)
    (η : A₀ ⟶ A₁) (θ : B₀ ⟶ B₁)
    (a : V₀ ⟶ A₀) (b : W₀ ⟶ B₀)
    (a' : V₁ ⟶ A₁) (b' : W₁ ⟶ B₁)
    (e : A₀ ⟶ B₀) (e' : A₁ ⟶ B₁)
    (f : V₀ ⟶ W₀) (f' : V₁ ⟶ W₁) (c : ℤ)
    (ha : u ≫ a' = a ≫ η) (hb : v ≫ b' = b ≫ θ)
    (he : η ≫ e' = e ≫ θ) (hf : u ≫ f' = f ≫ v)
    (hc : f ≫ b = c • (a ≫ e)) :
    c • (a' ≫ e') = f' ≫ b' := by
  apply (cancel_epi u).mp
  calc
    u ≫ (c • (a' ≫ e')) = c • ((u ≫ a') ≫ e') := by
      rw [Preadditive.comp_zsmul, Category.assoc]
    _ = c • (a ≫ e ≫ θ) := by rw [ha, Category.assoc, he]
    _ = (c • (a ≫ e)) ≫ θ := by rw [Preadditive.zsmul_comp, Category.assoc]
    _ = (f ≫ b) ≫ θ := by rw [hc]
    _ = (f ≫ v) ≫ b' := by rw [Category.assoc, Category.assoc, hb]
    _ = u ≫ (f' ≫ b') := by rw [← hf, Category.assoc]

end CategoryTheory
