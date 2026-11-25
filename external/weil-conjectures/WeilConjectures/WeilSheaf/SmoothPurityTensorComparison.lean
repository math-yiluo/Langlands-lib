/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.UnitProjection

/-! # Tensor products of compatible geometric and coefficient comparisons -/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory

variable {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory A] [MonoidalCategory B]
  (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ A) (I : A ⥤ B)
  [F.Monoidal] [G.Monoidal] [H.Monoidal] [I.Monoidal]
  (e : H ⋙ I ⟶ F ⋙ G) [e.IsMonoidal]

/-- The unit component of a monoidal comparison respects the inverse unit maps. -/
lemma purity_unit_comparison :
    e.app (𝟙_ C) ≫ G.map (η F) ≫ η G = I.map (η H) ≫ η I := by
  apply (cancel_epi (Functor.LaxMonoidal.ε (H ⋙ I))).mp
  rw [← Category.assoc, ← Category.assoc, NatTrans.IsMonoidal.unit]
  simp only [Category.assoc]
  change Functor.LaxMonoidal.ε (F ⋙ G) ≫ η (F ⋙ G) =
    Functor.LaxMonoidal.ε (H ⋙ I) ≫ η (H ⋙ I)
  simp only [Functor.Monoidal.ε_η]

/-- Compatible coefficient and geometric comparisons remain compatible under tensor
products. This applies in particular to all nonnegative powers of the Tate line. -/
lemma purity_tensor_comparison
    {M N : C} {M' N' : D} {P Q : A} {P' Q' : B}
    (u : F.obj M ⟶ M') (v : F.obj N ⟶ N')
    (r : H.obj M ⟶ P) (s : H.obj N ⟶ Q)
    (u' : I.obj P ⟶ P') (v' : I.obj Q ⟶ Q')
    (r' : G.obj M' ⟶ P') (s' : G.obj N' ⟶ Q')
    (hM : e.app M ≫ G.map u ≫ r' = I.map r ≫ u')
    (hN : e.app N ≫ G.map v ≫ s' = I.map s ≫ v') :
    e.app (M ⊗ N) ≫ G.map (δ F M N ≫ (u ⊗ₘ v)) ≫
        δ G M' N' ≫ (r' ⊗ₘ s') =
      I.map (δ H M N ≫ (r ⊗ₘ s)) ≫ δ I P Q ≫ (u' ⊗ₘ v') := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← δ_natural_assoc, ← δ_natural_assoc]
  have he := NatTrans.IsMonoidal.δ_comp_tensorHom e M N
  simp only [comp_δ, Functor.comp_obj, Category.assoc] at he
  rw [← reassoc_of% he]
  simp only [tensorHom_comp_tensorHom, hM, hN]

end CategoryTheory
