/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! # A pullback composition square detected at the legs of a limit -/

@[expose] public section

namespace CategoryTheory.Limits

/-- Composition compatibility at every term of a diagram gives compatibility
at its limit, provided the three comparison maps have the specified projections. -/
lemma purity_limit_pullback_composition
    {I A B C : Type*} [Category I] [Category A] [Category B] [Category C]
    (F : I ⥤ A) (G : I ⥤ B) (H : I ⥤ C)
    [HasLimit F] [HasLimit G] [HasLimit H]
    (P : A ⥤ B) (Q : B ⥤ C) (R : A ⥤ C) (a : R ≅ P ⋙ Q)
    (u : F ⋙ P ⟶ G) (v : G ⋙ Q ⟶ H) (w : F ⋙ R ⟶ H)
    (eP : P.obj (limit F) ⟶ limit G)
    (eQ : Q.obj (limit G) ⟶ limit H)
    (eR : R.obj (limit F) ⟶ limit H)
    (hP : ∀ i, eP ≫ limit.π G i = P.map (limit.π F i) ≫ u.app i)
    (hQ : ∀ i, eQ ≫ limit.π H i = Q.map (limit.π G i) ≫ v.app i)
    (hR : ∀ i, eR ≫ limit.π H i = R.map (limit.π F i) ≫ w.app i)
    (hw : ∀ i, a.hom.app (F.obj i) ≫ Q.map (u.app i) ≫ v.app i = w.app i) :
    a.hom.app (limit F) ≫ Q.map eP ≫ eQ = eR := by
  apply limit.hom_ext
  intro i
  have hn := a.hom.naturality (limit.π F i)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc, hQ]
  rw [← Q.map_comp_assoc, hP, Q.map_comp, ← Category.assoc,
    ← Category.assoc, ← hn, Category.assoc, Category.assoc, hw, hR]

end CategoryTheory.Limits
