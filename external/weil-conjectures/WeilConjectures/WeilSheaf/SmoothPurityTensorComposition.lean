/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Tensoring two pullback composition squares -/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory

/-- A compositor compatible with inverse tensorators composes tensor-product data. -/
lemma purity_tensor_composition
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal] (c : H ⟶ F ⋙ G)
    {M N : C} {M' N' : D} {M'' N'' : E}
    (u : F.obj M ⟶ M') (v : F.obj N ⟶ N')
    (u' : G.obj M' ⟶ M'') (v' : G.obj N' ⟶ N'')
    (w : H.obj M ⟶ M'') (z : H.obj N ⟶ N'')
    (hc : c.app (M ⊗ N) ≫ G.map (δ F M N) ≫ δ G (F.obj M) (F.obj N) =
      δ H M N ≫ (c.app M ⊗ₘ c.app N))
    (hM : c.app M ≫ G.map u ≫ u' = w)
    (hN : c.app N ≫ G.map v ≫ v' = z) :
    c.app (M ⊗ N) ≫ G.map (δ F M N ≫ (u ⊗ₘ v)) ≫
        δ G M' N' ≫ (u' ⊗ₘ v') = δ H M N ≫ (w ⊗ₘ z) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← δ_natural_assoc, reassoc_of% hc]
  simp only [tensorHom_comp_tensorHom, hM, hN]

end CategoryTheory
