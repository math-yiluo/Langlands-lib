/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.WeilEquivariance

/-! # Transporting a Weil datum through an object comparison -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category C] (G : C ⥤ C)

/-- The datum on the source of a comparison isomorphism induced by the target datum. -/
def purityConjugateWeilDatum {K' K : C} (e : K' ≅ K) (φ : G.obj K ⟶ K) :
    G.obj K' ⟶ K' := G.map e.hom ≫ φ ≫ e.inv

lemma purity_isWeilEquivariant_comparison_hom {K' K : C} (e : K' ≅ K)
    (φ : G.obj K ⟶ K) :
    IsWeilEquivariant G (purityConjugateWeilDatum G e φ) φ e.hom := by
  simp only [IsWeilEquivariant, purityConjugateWeilDatum, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

lemma purity_isWeilEquivariant_comparison_inv {K' K : C} (e : K' ≅ K)
    (φ : G.obj K ⟶ K) :
    IsWeilEquivariant G φ (purityConjugateWeilDatum G e φ) e.inv := by
  simp only [IsWeilEquivariant, purityConjugateWeilDatum, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp]

/-- Conjugating an equivariant isomorphism by the object comparisons returns an
equivariant isomorphism for the original data. -/
lemma purity_isWeilEquivariant_iso_transport {K' K L' L : C}
    (a : K' ≅ K) (b : L' ≅ L) (φK : G.obj K ⟶ K) (φL : G.obj L ⟶ L)
    (e : K' ≅ L')
    (he : IsWeilEquivariant G (purityConjugateWeilDatum G a φK)
      (purityConjugateWeilDatum G b φL) e.hom) :
    IsWeilEquivariant G φK φL (a.symm ≪≫ e ≪≫ b).hom :=
  (purity_isWeilEquivariant_comparison_inv G a φK).comp
    (he.comp (purity_isWeilEquivariant_comparison_hom G b φL))

end CategoryTheory
