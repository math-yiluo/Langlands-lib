/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Components of a named transported natural isomorphism -/

@[expose] public section

namespace CategoryTheory

/-- Compute a component after transporting an endofunctor, retaining the named isomorphism. -/
lemma purity_isoWhiskerLeft_symm_trans_app
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P L : D ⥤ D} (u : P ≅ L) (b : F ⋙ P ≅ F)
    (v : F ⋙ L ≅ F) (hv : v = Functor.isoWhiskerLeft F u.symm ≪≫ b) (M : C) :
    v.app M = (u.app (F.obj M)).symm ≪≫ b.app M := by
  subst v
  rfl

end CategoryTheory
