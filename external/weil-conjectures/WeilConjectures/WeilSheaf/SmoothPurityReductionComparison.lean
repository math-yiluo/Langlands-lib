/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Reading morphisms through a fully faithful reduction comparison -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- Keep the defining equation with the lifted isomorphism, so concrete applications need
only project the equation rather than elaborate a fully faithful preimage again. -/
def purityPreimageIsoWithHom
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    (hF : F.FullyFaithful) {X Y : C} (e : F.obj X ≅ F.obj Y) :
    {e' : X ≅ Y // F.map e'.hom = e.hom} :=
  ⟨hF.preimageIso e, hF.map_preimage e.hom⟩

/-- Transport an isomorphism across a comparison of reduction functors. -/
def purityReductionIso
    {C A D B : Type*} [Category C] [Category A] [Category D] [Category B]
    (J : C ⥤ A) (F : C ⥤ D) (I : D ⥤ B) (G : A ⥤ B)
    (α : F ⋙ I ≅ J ⋙ G) {K W : C} (e : F.obj K ≅ F.obj W) :
    G.obj (J.obj K) ≅ G.obj (J.obj W) :=
  (α.app K).symm ≪≫ I.mapIso e ≪≫ α.app W

/-- A reduction equation can be checked in the ambient category through its comparison iso. -/
lemma purity_reduction_map_eq_of_comparison
    {C A D B : Type*} [Category C] [Category A] [Category D] [Category B]
    (J : C ⥤ A) (F : C ⥤ D) (I : D ⥤ B) (G : A ⥤ B) (hI : I.FullyFaithful)
    (α : F ⋙ I ≅ J ⋙ G) {K W : C} (φ : K ⟶ W) (ψ : F.obj K ⟶ F.obj W)
    (h : G.map (J.map φ) = (α.app K).inv ≫ I.map ψ ≫ (α.app W).hom) :
    F.map φ = ψ := by
  apply hI.map_injective
  apply (cancel_mono (α.hom.app W)).mp
  change (F ⋙ I).map φ ≫ α.hom.app W = _
  rw [α.hom.naturality]
  change α.hom.app K ≫ G.map (J.map φ) = _
  rw [h]
  simp only [Iso.app_inv, Iso.app_hom, Iso.hom_inv_id_app_assoc]

end CategoryTheory
