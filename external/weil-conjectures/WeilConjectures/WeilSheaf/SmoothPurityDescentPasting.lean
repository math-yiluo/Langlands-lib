/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp

/-! # Normalization of pasted descent squares -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {A₀ A₁ A₂ W₀ W₁ W₂ C₀ C₁ C₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category W₀] [Category W₁] [Category W₂]
  [Category C₀] [Category C₁] [Category C₂]
  {L₁ : A₀ ⥤ A₁} {L₂ : A₁ ⥤ A₂}
  {T₀ : A₀ ⥤ W₀} {T₁ : A₁ ⥤ W₁} {T₂ : A₂ ⥤ W₂}
  {U₀ : W₀ ⥤ C₀} {U₁ : W₁ ⥤ C₁} {U₂ : W₂ ⥤ C₂}
  {P₀ : A₀ ⥤ C₀} {P₁ : A₁ ⥤ C₁} {P₂ : A₂ ⥤ C₂}
  {R₁ : C₀ ⥤ C₁} {R₂ : C₁ ⥤ C₂}
  {RW₁ : W₀ ⥤ W₁} {RW₂ : W₁ ⥤ W₂}

/-- Paste the descent squares of two successive direct images. -/
noncomputable def traceCompDescentIso (b₁ : T₀ ⋙ RW₁ ≅ L₁ ⋙ T₁)
    (b₂ : T₁ ⋙ RW₂ ≅ L₂ ⋙ T₂) : T₀ ⋙ (RW₁ ⋙ RW₂) ≅ (L₁ ⋙ L₂) ⋙ T₂ :=
  (associator _ _ _).symm ≪≫ isoWhiskerRight b₁ _ ≪≫
    associator _ _ _ ≪≫ isoWhiskerLeft _ b₂ ≪≫ (associator _ _ _).symm

/-- If two descent comparisons have the specified geometric carriers, so does
their composite. -/
lemma traceCompDescentIso_forget
    (a₀ : T₀ ⋙ U₀ ≅ P₀) (a₁ : T₁ ⋙ U₁ ≅ P₁) (a₂ : T₂ ⋙ U₂ ≅ P₂)
    (b₁ : T₀ ⋙ RW₁ ≅ L₁ ⋙ T₁) (b₂ : T₁ ⋙ RW₂ ≅ L₂ ⋙ T₂)
    (c₁ : RW₁ ⋙ U₁ ≅ U₀ ⋙ R₁) (c₂ : RW₂ ⋙ U₂ ≅ U₁ ⋙ R₂)
    (d₁ : L₁ ⋙ P₁ ≅ P₀ ⋙ R₁) (d₂ : L₂ ⋙ P₂ ≅ P₁ ⋙ R₂)
    (h₁ : ∀ M, d₁.hom.app M = a₁.inv.app (L₁.obj M) ≫ U₁.map (b₁.inv.app M) ≫
      c₁.hom.app (T₀.obj M) ≫ R₁.map (a₀.hom.app M))
    (h₂ : ∀ M, d₂.hom.app M = a₂.inv.app (L₂.obj M) ≫ U₂.map (b₂.inv.app M) ≫
      c₂.hom.app (T₁.obj M) ≫ R₂.map (a₁.hom.app M)) (K : A₀) :
    (Adjunction.compForgetIso d₁ d₂).hom.app K =
      a₂.inv.app ((L₁ ⋙ L₂).obj K) ≫
        U₂.map ((traceCompDescentIso b₁ b₂).inv.app K) ≫
        (Adjunction.compForgetIso c₁ c₂).hom.app (T₀.obj K) ≫
        (R₁ ⋙ R₂).map (a₀.hom.app K) := by
  simp only [Adjunction.compForgetIso, traceCompDescentIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerLeft_inv,
    isoWhiskerRight_hom, isoWhiskerRight_inv, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Functor.map_comp,
    Functor.comp_obj, Functor.comp_map, Category.id_comp, Category.comp_id, Category.assoc]
  rw [h₁, h₂]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R₂.map_comp_assoc, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, Functor.map_id, Category.id_comp]
  erw [← c₂.hom.naturality_assoc]
  rfl

end CategoryTheory.Functor
