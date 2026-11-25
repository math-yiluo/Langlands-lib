/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarDatumNamed

/-! # Scalar conjugation in the original descent representation -/

@[expose] public section

namespace CategoryTheory

/-- Keep the source equation in the natural-transformation component representation. -/
lemma purity_scalarDatum_conjugate_descent
    {C₀ C : Type*} [Category C₀] [Category C] [Preadditive C]
    (P : C₀ ⥤ C) (Q : C ⥤ C) (b : P ⋙ Q ≅ P)
    {M N : C₀} {T U : C} (α : P.obj M ≅ T) (β : P.obj N ≅ U)
    (t : Q.obj T ⟶ T) (u : Q.obj U ⟶ U)
    (ha : Q.map α.hom ≫ t = b.hom.app M ≫ α.hom)
    (hb : Q.map β.hom ≫ u = b.hom.app N ≫ β.hom)
    (e : P.obj M ≅ P.obj N) (v : T ≅ U) (hv : v = α.symm ≪≫ e ≪≫ β)
    (c : ℤ) (he : c • (b.hom.app M ≫ e.hom) = Q.map e.hom ≫ b.hom.app N) :
    c • (t ≫ v.hom) = Q.map v.hom ≫ u := by
  exact purity_scalarDatum_conjugate_named Q α β (b.hom.app M) (b.hom.app N)
    t u ha hb e v hv c he

end CategoryTheory
