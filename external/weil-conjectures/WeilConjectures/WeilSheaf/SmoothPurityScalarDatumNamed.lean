/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarDatumConjugation

/-! # Scalar conjugation with a named coordinate isomorphism -/

@[expose] public section

namespace CategoryTheory

/-- The conjugation law with its resulting isomorphism kept as a named argument. -/
lemma purity_scalarDatum_conjugate_named
    {C : Type*} [Category C] [Preadditive C] (Q : C ⥤ C)
    {A B T U : C} (α : A ≅ T) (β : B ≅ U)
    (a : Q.obj A ⟶ A) (b : Q.obj B ⟶ B)
    (t : Q.obj T ⟶ T) (u : Q.obj U ⟶ U)
    (ha : Q.map α.hom ≫ t = a ≫ α.hom)
    (hb : Q.map β.hom ≫ u = b ≫ β.hom)
    (e : A ≅ B) (v : T ≅ U) (hv : v = α.symm ≪≫ e ≪≫ β)
    (c : ℤ) (he : c • (a ≫ e.hom) = Q.map e.hom ≫ b) :
    c • (t ≫ v.hom) = Q.map v.hom ≫ u := by
  subst v
  exact purity_scalarDatum_conjugate Q α β a b t u ha hb e c he

end CategoryTheory
