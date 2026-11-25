/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Scalar Frobenius laws under a change of geometric coordinates -/

@[expose] public section

namespace CategoryTheory

/-- Transport a scalar Frobenius law through two equivariant isomorphisms. -/
lemma purity_scalarDatum_conjugate
    {C : Type*} [Category C] [Preadditive C] (Q : C ⥤ C)
    {A B T U : C} (α : A ≅ T) (β : B ≅ U)
    (a : Q.obj A ⟶ A) (b : Q.obj B ⟶ B)
    (t : Q.obj T ⟶ T) (u : Q.obj U ⟶ U)
    (ha : Q.map α.hom ≫ t = a ≫ α.hom)
    (hb : Q.map β.hom ≫ u = b ≫ β.hom)
    (e : A ≅ B) (c : ℤ) (he : c • (a ≫ e.hom) = Q.map e.hom ≫ b) :
    c • (t ≫ (α.symm ≪≫ e ≪≫ β).hom) =
      Q.map (α.symm ≪≫ e ≪≫ β).hom ≫ u := by
  apply (cancel_epi (Q.map α.hom)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Preadditive.comp_zsmul]
  rw [← Category.assoc, ha]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Q.map_comp_assoc, Iso.hom_inv_id, Q.map_id, Category.id_comp, hb]
  simpa only [Preadditive.zsmul_comp, Category.assoc] using
    congrArg (fun v ↦ v ≫ β.hom) he

/-- The scalar law with factor c is equivariance for the inverse scalar datum. -/
lemma purity_scalarDatum_inverse
    {C : Type*} [Category C] [Preadditive C] (Q : C ⥤ C)
    {T U : C} (t : Q.obj T ⟶ T) (u : Q.obj U ⟶ U)
    (e : T ⟶ U) (c : ℤ) (s : U ⟶ U)
    (he : c • (t ≫ e) = Q.map e ≫ u)
    (hs : (c • 𝟙 U) ≫ s = 𝟙 U) :
    Q.map e ≫ (u ≫ s) = t ≫ e := by
  rw [← Category.assoc, ← he, Preadditive.zsmul_comp,
    ← Preadditive.comp_zsmul]
  have hs' : c • s = 𝟙 U := by simpa only [Preadditive.zsmul_comp, Category.id_comp] using hs
  rw [hs', Category.comp_id]

end CategoryTheory
