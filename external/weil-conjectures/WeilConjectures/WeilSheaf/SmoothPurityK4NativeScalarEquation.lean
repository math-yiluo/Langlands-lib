/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarDatumNamed

/-! # A scalar equation interface with data arguments checked independently -/

@[expose] public section

namespace CategoryTheory.K4Native

/-- A scalar equation formed once in an abstract preadditive category. -/
def scalarEquation
    {C : Type*} [Category C] [Preadditive C] (Q : C ⥤ C)
    {A B : C} (a : Q.obj A ⟶ A) (b : Q.obj B ⟶ B) (e : A ≅ B) (c : ℤ) : Prop :=
  c • (a ≫ e.hom) = Q.map e.hom ≫ b

/-- Consume the scalar equation while the category and its objects remain abstract. -/
lemma scalarEquation_conjugate_named
    {C : Type*} [Category C] [Preadditive C] (Q : C ⥤ C)
    {A B T U : C} (α : A ≅ T) (β : B ≅ U)
    (a : Q.obj A ⟶ A) (b : Q.obj B ⟶ B)
    (t : Q.obj T ⟶ T) (u : Q.obj U ⟶ U)
    (ha : Q.map α.hom ≫ t = a ≫ α.hom)
    (hb : Q.map β.hom ≫ u = b ≫ β.hom)
    (e : A ≅ B) (v : T ≅ U) (hv : v = α.symm ≪≫ e ≪≫ β)
    (c : ℤ) (he : scalarEquation Q a b e c) :
    c • (t ≫ v.hom) = Q.map v.hom ≫ u := by
  exact purity_scalarDatum_conjugate_named Q α β a b t u ha hb e v hv c he

end CategoryTheory.K4Native
