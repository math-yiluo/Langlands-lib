/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Transport of scalar equations through equal whole isomorphisms -/

@[expose] public section

namespace CategoryTheory

/-- Keep the three isomorphisms as parameters while changing their presentations. -/
lemma purity_scalarDatum_transport_isos
    {C : Type*} [Category C] [Preadditive C] (Q : C ⥤ C)
    {A B : C} (a a' : Q.obj A ≅ A) (b b' : Q.obj B ≅ B)
    (e e' : A ≅ B) (ha : a' = a) (hb : b' = b) (he : e' = e) (c : ℤ)
    (h : c • (a.hom ≫ e.hom) = Q.map e.hom ≫ b.hom) :
    c • (a'.hom ≫ e'.hom) = Q.map e'.hom ≫ b'.hom := by
  subst a' b' e'
  exact h

/-- Replace a descent isomorphism before taking its component in a square. -/
lemma purity_square_transport_source_iso
    {C : Type*} [Category C] (Q : C ⥤ C) {A T : C}
    (α : A ⟶ T) (t : Q.obj T ⟶ T) (s s' : Q.obj A ≅ A) (hs : s = s')
    (h : Q.map α ≫ t = s.hom ≫ α) :
    Q.map α ≫ t = s'.hom ≫ α := by
  rw [← hs]
  exact h

end CategoryTheory
